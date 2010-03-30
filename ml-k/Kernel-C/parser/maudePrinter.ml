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
open DefaultMaudePrinter

(* Pretty's api can be found in cil/ocamlutil/pretty.mli *)

let (+^) (d1:Pretty.doc) (d2:string) : Pretty.doc = d1 ++ text d2
let (^+) (d1:string) (d2:Pretty.doc) : Pretty.doc = text d1 ++ d2
let sp : Pretty.doc = (text " ")

let paren (d:Pretty.doc) : Pretty.doc = "(" ^+ d +^ ")"
let giveType (d1:Pretty.doc) (d2:string) : Pretty.doc = paren(d1) ++ (text d2)

class maudePrinter = object(self)
	inherit defaultMaudePrinterClass as super
	
	method private pFunVariableDecl vi =
		giveType (self#pVDecl () vi ++ text ";") ".Declaration"
		
	method private pVDecl_storage x = 
		x
	method private pType_parts d1 d2 d3 =
		paren (d1 ++ sp ++ d2 ++ sp ++ d3)

	method private pInstr_parts d1 d2 d3 d4 = 
		(*text "(" ++ d1 ++ text ")" ++ text "(" ++ d2 ++ text ")" ++ text "(" ++ d3 ++ text ")"*)
		d1 ++ paren (d2 ++ sp ++ d3 ++ sp ++ d4)
		
	(* Invoked for each variable declaration. Note that variable declarations are all the 
	[GVar], [GVarDecl], [GFun], all the [varinfo] in formals of function types, and the 
	formals and locals for function definitions. *)
	(*method pVDecl () v = paren (super#pVDecl () v)(*giveType (super#pVDecl () v) ".Parameter-Declaration"*)*)

	(* Invoked on each variable use. *)
	(*method pVar (v:varinfo) : doc = giveType (super#pVar v) ".Identifier"*)
    
	(* Invoked on each lvalue occurence *)
	method pLval () lv = paren(super#pLval () lv)

	(*method pOffset: doc -> offset -> doc*)
	(** Invoked on each offset occurence. The second argument is the base. *)

	(* Invoked on each instruction occurrence. *)
	method pInstr () i = paren (super#pInstr () i) (*giveType (super#pInstr () i) ".Statement"*)
    
	(* Control-flow statement. This is used by  {!Cil.printGlobal} and by {!Cil.dumpGlobal}. *)
	method pStmt () st = paren(super#pStmt () st)

	method pBlock () bl = paren(super#pBlock () bl)
    (** Print a block. *)

	(** Global (vars, types, etc.). This can be slow and is used only by 
     * {!Cil.printGlobal} but by {!Cil.dumpGlobal} for everything else except 
     * [GVar] and [GFun]. *)
	method pGlobal () gl = paren ((paren (super#pGlobal () gl)) ++ text " ;; ")
    
	(** A field declaration *)
	method pFieldDecl () fi = paren (super#pFieldDecl () fi)
    
	(** Print a statement kind. The code to be printed is given in the
     * {!Cil.stmtkind} argument.  The initial {!Cil.stmt} argument
     * records the statement which follows the one being printed;
     * {!Cil.defaultCilPrinterClass} uses this information to prettify
     * statement printing in certain special cases. *)
	(* includes (return 0;) *)
	method pStmtKind st () stk = paren(super#pStmtKind st () stk) (*: stmt -> unit -> stmtkind -> Pretty.doc*)
    
	
	(** Print expressions *) 
	method pExp () e = paren (super#pExp () e)
    
	
	
(*
  method setCurrentFormals : varinfo list -> unit

  method setPrintInstrTerminator : string -> unit
  method getPrintInstrTerminator : unit -> string

  method pVDecl: unit -> varinfo -> doc
    (** Invoked for each variable declaration. Note that variable 
     * declarations are all the [GVar], [GVarDecl], [GFun], all the [varinfo] 
     * in formals of function types, and the formals and locals for function 
     * definitions. *)

  method pVar: varinfo -> doc
    (** Invoked on each variable use. *)

  method pLval: unit -> lval -> doc
    (** Invoked on each lvalue occurence *)

  method pOffset: doc -> offset -> doc
    (** Invoked on each offset occurence. The second argument is the base. *)

  method pInstr: unit -> instr -> doc
    (** Invoked on each instruction occurrence. *)

  method pStmt: unit -> stmt -> doc
    (** Control-flow statement. This is used by 
     * {!Cil.printGlobal} and by {!Cil.dumpGlobal}. *)

  method dStmt: out_channel -> int -> stmt -> unit
    (** Dump a control-flow statement to a file with a given indentation. This is used by 
     * {!Cil.dumpGlobal}. *)

  method dBlock: out_channel -> int -> block -> unit
    (** Dump a control-flow block to a file with a given indentation. This is 
     * used by {!Cil.dumpGlobal}. *)

  method pBlock: unit -> block -> Pretty.doc
    (** Print a block. *)

  method pGlobal: unit -> global -> doc
    (** Global (vars, types, etc.). This can be slow and is used only by 
     * {!Cil.printGlobal} but by {!Cil.dumpGlobal} for everything else except 
     * [GVar] and [GFun]. *)

  method dGlobal: out_channel -> global -> unit
    (** Dump a global to a file. This is used by {!Cil.dumpGlobal}. *)

  method pFieldDecl: unit -> fieldinfo -> doc
    (** A field declaration *)

  method pType: doc option -> unit -> typ -> doc  
  (* Use of some type in some declaration. The first argument is used to print 
   * the declared element, or is None if we are just printing a type with no 
   * name being declared. Note that for structure/union and enumeration types 
   * the definition of the composite type is not visited. Use [vglob] to 
   * visit it.  *)

  method pAttr: attribute -> doc * bool
    (** Attribute. Also return an indication whether this attribute must be 
      * printed inside the __attribute__ list or not. *)
   
  method pAttrParam: unit -> attrparam -> doc 
    (** Attribute paramter *)
   
  method pAttrs: unit -> attributes -> doc
    (** Attribute lists *)

  method pLabel: unit -> label -> doc
    (** Label *)

  method pLineDirective: ?forcefile:bool -> location -> Pretty.doc
    (** Print a line-number. This is assumed to come always on an empty line. 
     * If the forcefile argument is present and is true then the file name 
     * will be printed always. Otherwise the file name is printed only if it 
     * is different from the last time time this function is called. The last 
     * file name is stored in a private field inside the cilPrinter object. *)

  method pStmtKind : stmt -> unit -> stmtkind -> Pretty.doc
    (** Print a statement kind. The code to be printed is given in the
     * {!Cil.stmtkind} argument.  The initial {!Cil.stmt} argument
     * records the statement which follows the one being printed;
     * {!Cil.defaultCilPrinterClass} uses this information to prettify
     * statement printing in certain special cases. *)

  method pExp: unit -> exp -> doc
    (** Print expressions *) 

  method pInit: unit -> init -> doc
    (** Print initializers. This can be slow and is used by 
     * {!Cil.printGlobal} but not by {!Cil.dumpGlobal}. *)

  method dInit: out_channel -> int -> init -> unit
  *)
end

