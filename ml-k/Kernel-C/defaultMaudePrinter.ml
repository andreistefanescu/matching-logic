(* based off of code in CIL, for C to maude *)

(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
 
open Cil
open Pretty

(* Pretty's api can be found in cil/ocamlutil/pretty.mli *)
let pTypeSig : (typ -> typsig) ref =
  ref (fun _ -> Errormsg.s (Errormsg.bug "pTypeSig not initialized"))

class virtual defaultMaudePrinterClass = object (self) 
	inherit defaultCilPrinterClass as super
	
  (*** VARIABLES ***)
  (* variable use *)
 (* method pVar (v:varinfo) = text v.vname
*)
  (* variable declaration *)
  
	method virtual private pFunVariableDecl : 'a -> doc
	method virtual private pVDecl_storage : doc -> doc
	method virtual private pType_parts : doc -> doc -> doc -> doc
	method virtual private pInstr_parts : doc -> doc -> doc -> doc -> doc
	
	method pVDecl () (v:varinfo) =
		let stom, rest = separateStorageModifiers v.vattr in
		(* First the storage modifiers *)
		text (if v.vinline then "__inline " else "")
		  ++ self#pVDecl_storage (d_storage () v.vstorage)
		  ++ (self#pAttrs () stom)
		  ++ (self#pType (Some (text v.vname)) () v.vtype)
		  ++ text " "
		  ++ self#pAttrs () rest

	method pType (nameOpt: doc option) () (t:typ) =
	    let name = match nameOpt with None -> nil | Some d -> d in
	    let printAttributes (a: attributes) = 
			let pa = self#pAttrs () a in
			match nameOpt with 
			| None -> if pa = nil then nil else text "/*" ++ pa ++ text "*/"
			| _ -> pa
	    in
		match t with 
			TVoid a -> self#pType_parts (text "void") (printAttributes a) name
	    | TInt (ikind,a) -> self#pType_parts (d_ikind () ikind) (printAttributes a) name
	    | TFloat(fkind, a) -> self#pType_parts (d_fkind () fkind) (printAttributes a) name
	    | TComp (comp, a) -> (* A reference to a struct *)
	        let su = if comp.cstruct then "struct" else "union" in
			self#pType_parts (text (su ^ " " ^ comp.cname ^ " ")) (printAttributes a) name
	    | TEnum (enum, a) -> self#pType_parts (text ("enum " ^ enum.ename ^ " ")) (printAttributes a) name
		| TNamed (t, a) -> self#pType_parts (text t.tname) (printAttributes a) name
		| TBuiltin_va_list a -> self#pType_parts (text "__builtin_va_list") (printAttributes a) name
	    | _ -> super#pType nameOpt () t

 
	
(*
  (*** L-VALUES ***)
  method pLval () (lv:lval) =  (* lval (base is 1st field)  *)
    match lv with
      Var vi, o -> self#pOffset (self#pVar vi) o
    | Mem e, Field(fi, o) ->
        self#pOffset
          ((self#pExpPrec arrowLevel () e) ++ text ("->" ^ fi.fname)) o
    | Mem e, NoOffset -> 
        text "*" ++ self#pExpPrec derefStarLevel () e
    | Mem e, o ->
        self#pOffset
          (text "( ***********" ++ self#pExpPrec derefStarLevel () e ++ text ")") o
*)
  (** Offsets **)
  (*
  method pOffset (base: doc) = function
    | NoOffset -> base
    | Field (fi, o) -> 
        self#pOffset (base ++ text "." ++ text fi.fname) o
    | Index (e, o) ->
        self#pOffset (base ++ text "[" ++ self#pExp () e ++ text "]") o
*)
  method private pLvalPrec (contextprec: int) () lv = 
    if getParenthLevel (Lval(lv)) >= contextprec then
      text "(" ++ self#pLval () lv ++ text ")"
    else
      self#pLval () lv


  (*
  method pExp () (e: exp) : doc = 
    let level = getParenthLevel e in
    match e with
    (*  Const(c) -> d_const () c
    | Lval(l) -> self#pLval () l
    | UnOp(u,e1,_) -> 
        (d_unop () u) ++ chr ' ' ++ (self#pExpPrec level () e1)
    | BinOp(b,e1,e2,_) -> 
        align 
          ++ (self#pExpPrec level () e1)
          ++ chr ' ' 
          ++ (d_binop () b)
          ++ chr ' '
          ++ (self#pExpPrec level () e2)
          ++ unalign
    | CastE(t,e) -> 
        text "(" 
          ++ self#pType None () t
          ++ text ")"
          ++ self#pExpPrec level () e
    | SizeOf (t) -> 
        text "sizeof(" ++ self#pType None () t ++ chr ')'
    | SizeOfE (Lval (Var fv, NoOffset)) when fv.vname = "__builtin_va_arg_pack" && (not !printCilAsIs) -> 
        text "__builtin_va_arg_pack()"
    | SizeOfE (e) ->  
        text "sizeof(" ++ self#pExp () e ++ chr ')'
    | SizeOfStr s -> 
        text "sizeof(" ++ d_const () (CStr s) ++ chr ')'
    | AlignOf (t) -> 
        text "__alignof__(" ++ self#pType None () t ++ chr ')'
    | AlignOfE (e) -> 
        text "__alignof__(" ++ self#pExp () e ++ chr ')'
    | AddrOf(lv) -> 
        text "& " ++ (self#pLvalPrec addrOfLevel () lv)
    | StartOf(lv) -> self#pLval () lv *)
	| _ -> super#pExp () e
*)
(*
  (* Print an expression, given the precedence of the context in which it 
   * appears. *)
  method private pExpPrec (contextprec: int) () (e: exp) = 
    let thisLevel = getParenthLevel e in
    let needParens =
      if thisLevel >= contextprec then
	true
      else if contextprec == bitwiseLevel then
        (* quiet down some GCC warnings *)
	thisLevel == additiveLevel || thisLevel == comparativeLevel
      else
	false
    in
    if needParens then
      chr '(' ++ self#pExp () e ++ chr ')'
    else
      self#pExp () e

  method pInit () = function 
      SingleInit e -> self#pExp () e
    | CompoundInit (t, initl) -> 
      (* We do not print the type of the Compound *)
(*
      let dinit e = d_init () e in
      dprintf "{@[%a@]}"
        (docList ~sep:(chr ',' ++ break) dinit) initl
*)
        let printDesignator = 
          if not !msvcMode then begin
            (* Print only for union when we do not initialize the first field *)
            match unrollType t, initl with
              TComp(ci, _), [(Field(f, NoOffset), _)] -> 
                if not (ci.cstruct) && ci.cfields != [] && 
                  (List.hd ci.cfields) != f then
                  true
                else
                  false
            | _ -> false
          end else 
            false 
        in
        let d_oneInit = function
            Field(f, NoOffset), i -> 
              (if printDesignator then 
                text ("." ^ f.fname ^ " = ") 
              else nil) ++ self#pInit () i
          | Index(e, NoOffset), i -> 
              (if printDesignator then 
                text "[" ++ self#pExp () e ++ text "] = " else nil) ++ 
                self#pInit () i
          | _ -> Errormsg.s (unimp "Trying to print malformed initializer")
        in
        chr '{' ++ (align 
                      ++ ((docList ~sep:(chr ',' ++ break) d_oneInit) () initl) 
                      ++ unalign)
          ++ chr '}'
(*
    | ArrayInit (_, _, il) -> 
        chr '{' ++ (align 
                      ++ ((docList (chr ',' ++ break) (self#pInit ())) () il) 
                      ++ unalign)
          ++ chr '}'
*)
  (* dump initializers to a file. *)
  method dInit (out: out_channel) (ind: int) (i: init) = 
    (* Dump an array *)
    let dumpArray (bt: typ) (il: 'a list) (getelem: 'a -> init) = 
      let onALine = (* How many elements on a line *)
        match unrollType bt with TComp _ | TArray _ -> 1 | _ -> 4
      in
      let rec outputElements (isfirst: bool) (room_on_line: int) = function
          [] -> output_string out "}"
        | (i: 'a) :: rest -> 
            if not isfirst then output_string out ", ";
            let new_room_on_line = 
              if room_on_line == 0 then begin 
                output_string out "\n"; output_string out (String.make ind ' ');
                onALine - 1
              end else 
                room_on_line - 1
            in
            self#dInit out (ind + 2) (getelem i);
            outputElements false new_room_on_line rest
      in
      output_string out "{ ";
      outputElements true onALine il
    in
    match i with 
      SingleInit e -> 
        fprint out !lineLength (indent ind (self#pExp () e))
    | CompoundInit (t, initl) -> begin 
        match unrollType t with 
          TArray(bt, _, _) -> 
            dumpArray bt initl (fun (_, i) -> i)
        | _ -> 
            (* Now a structure or a union *)
            fprint out !lineLength (indent ind (self#pInit () i))
    end
(*
    | ArrayInit (bt, len, initl) -> begin
        (* If the base type does not contain structs then use the pInit 
        match unrollType bt with 
          TComp _ | TArray _ -> 
            dumpArray bt initl (fun x -> x)
        | _ -> *)
            fprint out !lineLength (indent ind (self#pInit () i))
    end
*)
*)       
  (** What terminator to print after an instruction. sometimes we want to 
   * print sequences of instructions separated by comma *)
  (*val mutable printInstrTerminator = ";"*)

  (*** INSTRUCTIONS ****)
  method pInstr () (i:instr) =       (* imperative instruction *)
    match i with
    | Set(lv,e,l) -> begin
        (* Be nice to some special cases *)
        (match e with
          BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(one,_,_)),_)
            when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
				self#pInstr_parts 
					(self#pLineDirective l) 
					(self#pLvalPrec indexLevel () lv)
	                (text (" ++" ))
					(text "")
        | BinOp((MinusA|MinusPI),Lval(lv'),
                Const(CInt64(one,_,_)), _) 
            when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
				self#pInstr_parts 
					(self#pLineDirective l) 
					(self#pLvalPrec indexLevel () lv)
	                (text (" --" ))
					(text "")
        | BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(mone,_,_)),_)
            when Util.equals lv lv' && mone = Int64.minus_one 
                && not !printCilAsIs ->
					self#pInstr_parts 
						(self#pLineDirective l) 
						(self#pLvalPrec indexLevel () lv)
		                (text (" --" ))
						(text "")
        | BinOp((PlusA|PlusPI|IndexPI|MinusA|MinusPP|MinusPI|BAnd|BOr|BXor|
          Mult|Div|Mod|Shiftlt|Shiftrt) as bop,
                Lval(lv'),e,_) when Util.equals lv lv' 
                && not !printCilAsIs ->
					self#pInstr_parts 
						(self#pLineDirective l) 
						(self#pLval () lv)
						(text " " ++ d_binop () bop ++ text "= ")
		                (self#pExp () e)
        | _ ->
			self#pInstr_parts 
				(self#pLineDirective l) 
				(self#pLval () lv)
				(text " = ")
				(self#pExp () e)
		) ++ text (super#getPrintInstrTerminator ())
              
    end
      (* In cabs2cil we have turned the call to builtin_va_arg into a 
       * three-argument call: the last argument is the address of the 
       * destination *)
	| Call(dest,e,args,l) ->
		self#pLineDirective l
		  ++ (match dest with
			None -> nil
		  | Some lv -> 
			  text "(" ++ self#pLval () lv ++ text " = " ++
				(* Maybe we need to print a cast *)
				(let destt = typeOfLval lv in
				match unrollType (typeOf e) with
					(* Now the cast *)
				  TFun (rt, _, _, _)
					  (*when not (Util.equals (!pTypeSig rt)
											(!pTypeSig destt)) *)->
					text "`(_`)_((" ++ self#pType None () destt ++ text "),"
				| _ -> text "("))
		  (* Now the function name *)
		  ++ text "(" ++ (let ed = self#pExp () e in
			  match e with 
				Lval(Var _, _) -> ed
			  | _ -> text "(" ++ ed ++ text ")")
		  ++ text "(" ++ 
		  (align
			 (* Now the arguments *)
			 ++ (docList ~sep:(chr ',' ++ break) 
				   (self#pExp ()) () args)
			 ++ unalign)
		++ text ("))))" ^ (super#getPrintInstrTerminator ()))
    | _ -> super#pInstr () i
			
			
	(*

  (**** STATEMENTS ****)
  method pStmt () (s:stmt) =        (* control-flow statement *)
    self#pStmtNext invalidStmt () s

  method dStmt (out: out_channel) (ind: int) (s:stmt) : unit = 
    fprint out !lineLength (indent ind (self#pStmt () s))

  method dBlock (out: out_channel) (ind: int) (b:block) : unit = 
    fprint out !lineLength (indent ind (align ++ self#pBlock () b))

  method private pStmtNext (next: stmt) () (s: stmt) =
    (* print the labels *)
    ((docList ~sep:line (fun l -> self#pLabel () l)) () s.labels)
      (* print the statement itself. If the labels are non-empty and the
      * statement is empty, print a semicolon  *)
      ++ 
      (if s.skind = Instr [] && s.labels <> [] then
        text ";"
      else
        (if s.labels <> [] then line else nil) 
          ++ self#pStmtKind next () s.skind)

  method private pLabel () = function
      Label (s, _, true) -> text (s ^ ": ")
    | Label (s, _, false) -> text (s ^ ": /* CIL Label */ ")
    | Case (e, _) -> text "case " ++ self#pExp () e ++ text ": "
    | Default _ -> text "default: "

  (* The pBlock will put the unalign itself *)
  method pBlock () (blk: block) = 
    let rec dofirst () = function
        [] -> nil
      | [x] -> self#pStmtNext invalidStmt () x
      | x :: rest -> dorest nil x rest
    and dorest acc prev = function
        [] -> acc ++ (self#pStmtNext invalidStmt () prev)
      | x :: rest -> 
          dorest (acc ++ (self#pStmtNext x () prev) ++ line)
            x rest
    in
    (* Let the host of the block decide on the alignment. The d_block will 
     * pop the alignment as well  *)
    text "{" 
      ++ 
      (if blk.battrs <> [] then 
        self#pAttrsGen true blk.battrs
      else nil)
      ++ line
      ++ (dofirst () blk.bstmts)
      ++ unalign ++ line ++ text "}"

  
  (* Store here the name of the last file printed in a line number. This is 
   * private to the object *)
  val mutable lastFileName = ""
  val mutable lastLineNumber = -1

  (* Make sure that you only call self#pLineDirective on an empty line *)
  method pLineDirective ?(forcefile=false) l = 
    currentLoc := l;
    match !lineDirectiveStyle with
    | None -> nil
    | Some _ when l.line <= 0 -> nil

      (* Do not print lineComment if the same line as above *)
    | Some LineCommentSparse when l.line = lastLineNumber -> nil

    | Some style  ->
	let directive =
	  match style with
	  | LineComment | LineCommentSparse -> text "//#line "
	  | LinePreprocessorOutput when not !msvcMode -> chr '#'
	  | LinePreprocessorOutput | LinePreprocessorInput -> text "#line"
	in
        lastLineNumber <- l.line; 
	let filename =
          if forcefile || l.file <> lastFileName then
	    begin
	      lastFileName <- l.file;
	      text " \"" ++ text l.file ++ text "\""
            end
	  else
	    nil
	in
	leftflush ++ directive ++ chr ' ' ++ num l.line ++ filename ++ line

*)
  method private pStmtKind (next: stmt) () = function
      Return(None, l) ->
        self#pLineDirective l
          ++ text "return;"
    | Return(Some e, l) ->
        self#pLineDirective l
          ++ text "return ("
          ++ self#pExp () e
          ++ text ");"
    | Goto (sref, l) -> begin
        (* Grab one of the labels *)
        let rec pickLabel = function
            [] -> None
          | Label (l, _, _) :: _ -> Some l
          | _ :: rest -> pickLabel rest
        in
        match pickLabel !sref.labels with
          Some l -> text ("goto " ^ l ^ ";")
        | None -> 
            ignore (error "Cannot find label for target of goto");
            text "goto __invalid_label;"
    end
    | Break l ->
        self#pLineDirective l
          ++ text "break ;"
    | Continue l -> 
        self#pLineDirective l
          ++ text "continue ;"
    | Instr il ->
        align
          ++ (docList ~sep:line (fun i -> self#pInstr () i) () il)
          ++ unalign

    | If(be,t,{bstmts=[];battrs=[]},l) when not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () be
                ++ text ") "
                ++ self#pBlock () t)
          
    | If(be,t,{bstmts=[{skind=Goto(gref,_);labels=[]}];
                battrs=[]},l)
     when !gref == next && not !printCilAsIs ->
       self#pLineDirective l
         ++ text "if"
         ++ (align
               ++ text " ("
               ++ self#pExp () be
               ++ text ") "
               ++ self#pBlock () t)

    | If(be,{bstmts=[];battrs=[]},e,l) when not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)

    | If(be,{bstmts=[{skind=Goto(gref,_);labels=[]}];
           battrs=[]},e,l)
      when !gref == next && not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)
          
    | If(be,t,e,l) ->
        self#pLineDirective l
          ++ (align
                ++ text "if"
                ++ (align
                      ++ text " ("
                      ++ self#pExp () be
                      ++ text ") "
                      ++ self#pBlock () t)
                ++ text " "   (* sm: indent next code 2 spaces (was 4) *)
                ++ (align
                      ++ text "else "
                      ++ self#pBlock () e)
          ++ unalign)
          
    | Switch(e,b,_,l) ->
        self#pLineDirective l
          ++ (align
                ++ text "switch ("
                ++ self#pExp () e
                ++ text ") "
                ++ self#pBlock () b)
    | Loop(b, l, _, _) -> begin
        (* Maybe the first thing is a conditional. Turn it into a WHILE *)
        try
          let term, bodystmts =
            let rec skipEmpty = function
                [] -> []
              | {skind=Instr [];labels=[]} :: rest -> skipEmpty rest
              | x -> x
            in
            (* Bill McCloskey: Do not remove the If if it has labels *)
            match skipEmpty b.bstmts with
              {skind=If(e,tb,fb,_); labels=[]} :: rest 
                                              when not !printCilAsIs -> begin
                match skipEmpty tb.bstmts, skipEmpty fb.bstmts with
                  [], {skind=Break _; labels=[]} :: _  -> e, rest
                | {skind=Break _; labels=[]} :: _, [] 
                                     -> UnOp(LNot, e, intType), rest
                | _ -> raise Not_found
              end
            | _ -> raise Not_found
          in
          self#pLineDirective l
            ++ text "wh"
            ++ (align
                  ++ text "ile ("
                  ++ self#pExp () term
                  ++ text ") "
                  ++ self#pBlock () {bstmts=bodystmts; battrs=b.battrs})

        with Not_found ->
          self#pLineDirective l
            ++ text "wh"
            ++ (align
                  ++ text "ile (1) "
                  ++ self#pBlock () b)
    end
    | Block b -> align ++ self#pBlock () b
      
    | TryFinally (b, h, l) -> 
        self#pLineDirective l 
          ++ text "__try "
          ++ align 
          ++ self#pBlock () b
          ++ text " __fin" ++ align ++ text "ally "
          ++ self#pBlock () h

    | TryExcept (b, (il, e), h, l) -> 
        self#pLineDirective l 
          ++ text "__try "
          ++ align 
          ++ self#pBlock () b
          ++ text " __e" ++ align ++ text "xcept(" ++ line
          ++ align
          (* Print the instructions but with a comma at the end, instead of 
           * semicolon *)
          ++ (super#setPrintInstrTerminator ","; 
              let res = 
                (docList ~sep:line (self#pInstr ())
                   () il) 
              in
              super#setPrintInstrTerminator ";";
              res)
          ++ self#pExp () e
          ++ text ") " ++ unalign
          ++ self#pBlock () h

(*
method pGlobal() (g:global) : doc =
	text ""
*)

	(*** because i don't understand ocaml's dispatch, adding this (copy of above) here *)
  (*** GLOBALS ***)
  method pGlobal () (g:global) : doc =       (* global (vars, types, etc.) *)
    match g with 
    | GFun (fundec, l) ->
        (* If the function has attributes then print a prototype because 
        * GCC cannot accept function attributes in a definition *)
        let oldattr = fundec.svar.vattr in
        (* Always pring the file name before function declarations *)
        let proto = 
          if oldattr <> [] then 
            (self#pLineDirective l) ++ (self#pVDecl () fundec.svar) 
              ++ chr ';' ++ line 
          else nil in
        (* Temporarily remove the function attributes *)
        fundec.svar.vattr <- [];
        let body = (self#pLineDirective ~forcefile:true l) 
                      ++ (self#pFunDecl () fundec) in
        fundec.svar.vattr <- oldattr;
        proto ++ body ++ line
	| _ -> (super#pGlobal () g)

(*
    | GType (typ, l) ->
        self#pLineDirective ~forcefile:true l ++
          text "typedef "
          ++ (self#pType (Some (text typ.tname)) () typ.ttype)
          ++ text ";\n"

    | GEnumTag (enum, l) ->
        self#pLineDirective l ++
          text "enum" ++ align ++ text (" " ^ enum.ename) ++
          text " {" ++ line
          ++ (docList ~sep:(chr ',' ++ line)
                (fun (n,i, loc) -> 
                  text (n ^ " = ") 
                    ++ self#pExp () i)
                () enum.eitems)
          ++ unalign ++ line ++ text "} " 
          ++ self#pAttrs () enum.eattr ++ text";\n"

    | GEnumTagDecl (enum, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text ("enum " ^ enum.ename ^ ";\n")

    | GCompTag (comp, l) -> (* This is a definition of a tag *)
        let n = comp.cname in
        let su, su1, su2 =
          if comp.cstruct then "struct", "str", "uct"
          else "union",  "uni", "on"
        in
        let sto_mod, rest_attr = separateStorageModifiers comp.cattr in
        self#pLineDirective ~forcefile:true l ++
          text su1 ++ (align ++ text su2 ++ chr ' ' ++ (self#pAttrs () sto_mod)
                         ++ text n
                         ++ text " {" ++ line
                         ++ ((docList ~sep:line (self#pFieldDecl ())) () 
                               comp.cfields)
                         ++ unalign)
          ++ line ++ text "}" ++
          (self#pAttrs () rest_attr) ++ text ";\n"

    | GCompTagDecl (comp, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text (compFullName comp) ++ text ";\n"

    | GVar (vi, io, l) ->
        self#pLineDirective ~forcefile:true l ++
          self#pVDecl () vi
          ++ chr ' '
          ++ (match io.init with
            None -> nil
          | Some i -> text " = " ++ 
                (let islong = 
                  match i with
                    CompoundInit (_, il) when List.length il >= 8 -> true
                  | _ -> false 
                in
                if islong then 
                  line ++ self#pLineDirective l ++ text "  " 
                else nil) ++
                (self#pInit () i))
          ++ text ";\n"
      
    (* print global variable 'extern' declarations, and function prototypes *)    
    | GVarDecl (vi, l) ->
        if not !printCilAsIs && H.mem builtinFunctions vi.vname then begin
          (* Compiler builtins need no prototypes. Just print them in
             comments. *)
          text "/* compiler builtin: \n   " ++
            (self#pVDecl () vi)
            ++ text ";  */\n"
          
        end else
          self#pLineDirective l ++
            (self#pVDecl () vi)
            ++ text ";\n"

    | GAsm (s, l) ->
        self#pLineDirective l ++
          text ("__asm__(\"" ^ escape_string s ^ "\");\n")

    | GPragma (Attr(an, args), l) ->
        (* sm: suppress printing pragmas that gcc does not understand *)
        (* assume anything starting with "ccured" is ours *)
        (* also don't print the 'combiner' pragma *)
        (* nor 'cilnoremove' *)
        let suppress =
          not !print_CIL_Input && 
          not !msvcMode &&
          ((startsWith "box" an) ||
           (startsWith "ccured" an) ||
           (an = "merger") ||
           (an = "cilnoremove")) in
        let d =
	  match an, args with
	  | _, [] ->
              text an
	  | "weak", [ACons (symbol, [])] ->
	      text "weak " ++ text symbol
	  | _ ->
            text (an ^ "(")
              ++ docList ~sep:(chr ',') (self#pAttrParam ()) () args
              ++ text ")"
        in
        self#pLineDirective l 
          ++ (if suppress then text "/* " else text "")
          ++ (text "#pragma ")
          ++ d
          ++ (if suppress then text " */\n" else text "\n")

    | GText s  -> 
        if s <> "//" then 
          text s ++ text "\n"
        else
          nil
*)
	(* same as above *)
	method dGlobal (out: out_channel) (g: global) : unit =	
     (* For all except functions and variable with initializers, use the 
      * pGlobal *)
     match g with 
       GFun (fdec, l) -> 
         (* If the function has attributes then print a prototype because 
          * GCC cannot accept function attributes in a definition *)
         let oldattr = fdec.svar.vattr in
         let proto = 
           if oldattr <> [] then 
             (self#pLineDirective l) ++ (self#pVDecl () fdec.svar) 
               ++ chr ';' ++ line
           else nil in
         fprint out !lineLength
           (proto ++ (self#pLineDirective ~forcefile:true l));
         (* Temporarily remove the function attributes *)
         fdec.svar.vattr <- [];
         fprint out !lineLength (self#pFunDecl () fdec);               
         fdec.svar.vattr <- oldattr;
         output_string out "\n"
     | _ -> super#dGlobal out g
	
(*
   method pFieldDecl () fi = 
     (self#pType
        (Some (text (if fi.fname = missingFieldName then "" else fi.fname)))
        () 
        fi.ftype)
       ++ text " "
       ++ (match fi.fbitfield with None -> nil 
       | Some i -> text ": " ++ num i ++ text " ")
       ++ self#pAttrs () fi.fattr
       ++ text ";"
*)
  method private pFunDecl () f =
      text "((" 
	  ++ self#pVDecl () f.svar
      ++ line
      ++ text "{ "
      ++ (align
            (* locals. *)
            ++ (docList ~sep:line (self#pFunVariableDecl)
                  () f.slocals)
            ++ line ++ line
            (* the body *)
            ++ ((* remember the declaration *) super#setCurrentFormals f.sformals; 
                let body = self#pBlock () f.sbody in
                super#setCurrentFormals [];
                body))
      ++ line
      ++ text "}) ;;) "
(*
  (***** PRINTING DECLARATIONS and TYPES ****)
    


  (**** PRINTING ATTRIBUTES *********)
  method pAttrs () (a: attributes) = 
    self#pAttrsGen false a


  (* Print one attribute. Return also an indication whether this attribute 
   * should be printed inside the __attribute__ list *)
  method pAttr (Attr(an, args): attribute) : doc * bool =
    (* Recognize and take care of some known cases *)
    match an, args with 
      "const", [] -> text "const", false
          (* Put the aconst inside the attribute list *)
    | "aconst", [] when not !msvcMode -> text "__const__", true
    | "thread", [] when not !msvcMode -> text "__thread", false
(*
    | "used", [] when not !msvcMode -> text "__attribute_used__", false 
*)
    | "volatile", [] -> text "volatile", false
    | "restrict", [] -> text "__restrict", false
    | "missingproto", [] -> text "/* missing proto */", false
    | "cdecl", [] when !msvcMode -> text "__cdecl", false
    | "stdcall", [] when !msvcMode -> text "__stdcall", false
    | "fastcall", [] when !msvcMode -> text "__fastcall", false
    | "declspec", args when !msvcMode -> 
        text "__declspec(" 
          ++ docList (self#pAttrParam ()) () args
          ++ text ")", false
    | "w64", [] when !msvcMode -> text "__w64", false
    | "asm", args -> 
        text "__asm__(" 
          ++ docList (self#pAttrParam ()) () args
          ++ text ")", false
    (* we suppress printing mode(__si__) because it triggers an *)
    (* internal compiler error in all current gcc versions *)
    (* sm: I've now encountered a problem with mode(__hi__)... *)
    (* I don't know what's going on, but let's try disabling all "mode"..*)
    | "mode", [ACons(tag,[])] -> 
        text "/* mode(" ++ text tag ++ text ") */", false

    (* sm: also suppress "format" because we seem to print it in *)
    (* a way gcc does not like *)
    | "format", _ -> text "/* format attribute */", false

    (* sm: here's another one I don't want to see gcc warnings about.. *)
    | "mayPointToStack", _ when not !print_CIL_Input 
    (* [matth: may be inside another comment.]
      -> text "/*mayPointToStack*/", false 
    *)
      -> text "", false
    | "arraylen", [a] -> 
        (* text "/*[" ++ self#pAttrParam () a ++ text "]*/" *) nil, false


    | _ -> (* This is the dafault case *)
        (* Add underscores to the name *)
        let an' = if !msvcMode then "__" ^ an else "__" ^ an ^ "__" in
        if args = [] then 
          text an', true
        else
          text (an' ^ "(") 
            ++ (docList (self#pAttrParam ()) () args)
            ++ text ")", 
          true

  method private pAttrPrec (contextprec: int) () (a: attrparam) = 
    let thisLevel = getParenthLevelAttrParam a in
    let needParens =
      if thisLevel >= contextprec then
	true
      else if contextprec == bitwiseLevel then
        (* quiet down some GCC warnings *)
	thisLevel == additiveLevel || thisLevel == comparativeLevel
      else
	false
    in
    if needParens then
      chr '(' ++ self#pAttrParam () a ++ chr ')'
    else
      self#pAttrParam () a


  method pAttrParam () a = 
    let level = getParenthLevelAttrParam a in
    match a with 
    | AInt n -> num n
    | AStr s -> text ("\"" ^ escape_string s ^ "\"")
    | ACons(s, []) -> text s
    | ACons(s,al) ->
        text (s ^ "(")
          ++ (docList (self#pAttrParam ()) () al)
          ++ text ")"
    | ASizeOfE a -> text "sizeof(" ++ self#pAttrParam () a ++ text ")"
    | ASizeOf t -> text "sizeof(" ++ self#pType None () t ++ text ")"
    | ASizeOfS ts -> text "sizeof(<typsig>)"
    | AAlignOfE a -> text "__alignof__(" ++ self#pAttrParam () a ++ text ")"
    | AAlignOf t -> text "__alignof__(" ++ self#pType None () t ++ text ")"
    | AAlignOfS ts -> text "__alignof__(<typsig>)"
    | AUnOp(u,a1) -> 
        (d_unop () u) ++ chr ' ' ++ (self#pAttrPrec level () a1)

    | ABinOp(b,a1,a2) -> 
        align 
          ++ text "(" 
          ++ (self#pAttrPrec level () a1)
          ++ text ") "
          ++ (d_binop () b)
          ++ break 
          ++ text " (" ++ (self#pAttrPrec level () a2) ++ text ") "
          ++ unalign
    | ADot (ap, s) -> (self#pAttrParam () ap) ++ text ("." ^ s)
    | AStar a1 -> 
        text "(*" ++ (self#pAttrPrec derefStarLevel () a1) ++ text ")"
    | AAddrOf a1 -> text "& " ++ (self#pAttrPrec addrOfLevel () a1)
    | AIndex (a1, a2) -> self#pAttrParam () a1 ++ text "[" ++ 
                         self#pAttrParam () a2 ++ text "]"
    | AQuestion (a1, a2, a3) -> 
          self#pAttrParam () a1 ++ text " ? " ++
          self#pAttrParam () a2 ++ text " : " ++
          self#pAttrParam () a3 

 
  (* A general way of printing lists of attributes *)
  method private pAttrsGen (block: bool) (a: attributes) = 
    (* Scan all the attributes and separate those that must be printed inside 
     * the __attribute__ list *)
    let rec loop (in__attr__: doc list) = function
        [] -> begin 
          match in__attr__ with
            [] -> nil
          | _ :: _->
              (* sm: added 'forgcc' calls to not comment things out
               * if CIL is the consumer; this is to address a case
               * Daniel ran into where blockattribute(nobox) was being
               * dropped by the merger
               *)
              (if block then 
                text (" " ^ (forgcc "/*") ^ " __blockattribute__(")
               else
                 text "__attribute__((")

                ++ (docList ~sep:(chr ',' ++ break)
                      (fun a -> a)) () in__attr__
                ++ text ")"
                ++ (if block then text (forgcc "*/") else text ")")
        end
      | x :: rest -> 
          let dx, ina = self#pAttr x in
          if ina then 
            loop (dx :: in__attr__) rest
          else if dx = nil then
            loop in__attr__ rest
          else
            dx ++ text " " ++ loop in__attr__ rest
    in
    let res = loop [] a in
    if res = nil then
      res
    else
      text " " ++ res ++ text " "
*)
end (* class defaultCilPrinterClass *)
