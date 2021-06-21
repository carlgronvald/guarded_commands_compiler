﻿namespace GuardedCommands.Frontend
// Michael R. Hansen 05-01-2016, 07-06-2021
// This file is obtained by an adaption of the file MicroC/Absyn.fs by Peter Sestoft
//
// It must preceed TypeChecks.fs, CodeGen.fs, CodeGenOpt.fs, Util.fs in Solution Explorer
//

// Alterations:
//    Cconst, CTyp, PrintC: Carl Frederik Grønvald, 18/06/2021
//    Mass: Tobias Frederik Flensberg Thomsen, 14/06 - 18/06 2021
//    Inc, Dec: Nicolai Kornerup-Bang Melin: 18/06 - 21/06 2021

module AST =

   type Exp =                            
         | N  of int                   (* Integer constant            *)
         | B of bool                   (* Boolean constant            *)
         | Cconst of char              (* Char constant               *)
         | Access of Access            (* x    or  ^p    or  a[e]     *)
         | Addr of Access              (* &x   or  &p^   or  &a[e]    *)
         | Apply of string * Exp list  (* Function application        *)

   and Access = 
          | AVar of string             (* Variable access        x    *) 
          | AIndex of Access * Exp     (* Array indexing         a[e] *)
          | ADeref of Exp              (* Pointer dereferencing  p^   *)

   type Stm  =                            
          | PrintI of Exp                (* Print something as an integer  *) 
          | PrintC of Exp                (* Print something as a character*)
          | Ass of Access * Exp          (* x:=e  or  p^:=e  or  a[e]:=e   *)
          | Mass of Access list * Exp list 
          | Return of Exp option         (* Return from function           *)   
          | Alt of GuardedCommand        (* Alternative statement          *) 
          | Do of GuardedCommand         (* Repetition statement           *) 
          | Block of Dec list * Stm list (* Block: grouping and scope      *)
          | Call of string * Exp list    (* Procedure call                 *)
          | Inc of Access                (* ++i;                           *)
          | Dec of Access                (* --i;                           *)
               
   and GuardedCommand = GC of (Exp * Stm list) list (* Guarded commands    *)

   and Dec = 
         | VarDec of Typ * string        (* Variable declaration               *)
         | FunDec of Typ option * string * Dec list * Stm
                                         (* Function and procedure declaration *) 

   and Typ  = 
         | ITyp                          (* Type int                    *)
         | BTyp                          (* Type bool                   *)
         | CTyp                          (* Type char                   *)
         | ATyp of Typ * int option      (* Type array                  *)
         | PTyp of Typ                   (* Type pointer                *)
         | FTyp of Typ list * Typ option (* Type function and procedure *)

   type Program = P of Dec list * Stm list   (* Program                 *)
