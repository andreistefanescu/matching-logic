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

let replace input output =
    Str.global_replace (Str.regexp_string input) output


class maudeVisitor = object (self) inherit nopCilVisitor
	val mutable identifierList : string list = []
	val mutable typedefList : string list = []
	
	method getIdentifierList = identifierList
	method getTypedefList = typedefList
	
	method vvdec (v:varinfo) = begin
		(*print_string (v.vname ^ "\n");*)
		identifierList <- (replace "_" "u" v.vname) :: identifierList;
		DoChildren
	end

	method vvrbl (v:varinfo) = begin
		identifierList <- (replace "_" "u" v.vname) :: identifierList;
		DoChildren
	end
	
	method vglob (g:global) = begin
		( match g with 
			(* | GFun(fundec, l) -> begin
				let formalVisit = fun fi -> 
					print_string (fi.vname ^ "\n");
					identifierList <- (replace "_" "u" fi.vname) :: identifierList
				in List.iter formalVisit fundec.sformals;
			end *)
			| GType(typeinfo, location) -> typedefList <- (replace "_" "u" typeinfo.tname) :: typedefList
			| GVarDecl(varinfo, location) -> 
				identifierList <- (replace "_" "u" varinfo.vname) :: identifierList
			| GCompTag (comp, l) -> begin
				identifierList <- (replace "_" "u" comp.cname) :: identifierList;
				let fieldVisit = fun fi -> 
					(* print_string (fi.fname ^ "\n"); *)
					identifierList <- (replace "_" "u" fi.fname) :: identifierList
			      in
			      List.iter fieldVisit comp.cfields;
			      (*comp.cattr <- visitCilAttributes vis comp.cattr;*)
			end
			
			| _ -> ()
		) ;
		DoChildren
	end
	
	
	method vstmt (s: stmt) : stmt visitAction = 
		let labelVisit = fun fi -> match fi with 
			| Label (s, _, true) -> identifierList <- (replace "_" "u" s) :: identifierList
			| Label (s, _, false) -> identifierList <- (replace "_" "u" s) :: identifierList	
		in List.iter labelVisit s.labels;
		DoChildren
		
	
	(* method vattr: attribute -> attribute list visitAction  *)
	(* method vattr (Attr (s, params)) = begin
		identifierList <- (replace "_" "u" s) :: identifierList;
		print_string (s ^ "\n");
		DoChildren
	end *)
	
	method vinit (forg: varinfo) (off: offset) (i:init) = begin
		identifierList <- (replace "_" "u" forg.vname) :: identifierList;
		DoChildren
	end
	
	method vtype (t:typ) = begin
		( match t with 
			| TFun (restyp, args, isvararg, a) -> begin
				let argVisit = fun fi -> 
					match fi with
					| (aname, atype, aattr) -> 
						if (String.length(aname) != 0) then (
							identifierList <- (replace "_" "u" aname) :: identifierList;
						)
			      in match args with
					| Some xs -> List.iter argVisit xs
					| None -> () ;
			end
				 (* (match args with
				| Some ((aname, atype, aattr)::xs) -> 
					if (String.length(aname) != 0) then (
						identifierList <- (replace "_" "u" aname) :: identifierList;
					) else (
					)
				| _ -> () ; 
				)*)
			(* | TNamed (typeinfo, attributes) -> *)
			(* typedefList <- (replace "_" "u" typeinfo.tname) :: typedefList (*typeinfo.ttype*) *)
			| _ -> ()
		) ;
		DoChildren
	end
	
	
end