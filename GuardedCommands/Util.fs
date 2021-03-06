// Michael R. Hansen 05-01-2016, 04-01-2018, 07-06-2021

// Alterations: Carl Frederik Grønvald, 18/06 - 21/06 2021 (Create timed run functions)

namespace GuardedCommands.Util


open System.IO
open System.Text
open Microsoft.FSharp.Text.Lexing


open Parser
open Machine
open VirtualMachine


module ParserUtil = 

   let parseString (text:string) =
      let lexbuf = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(text))
      try
           Main Lexer.tokenize lexbuf
      with e ->
           let pos = lexbuf.EndPos
           printfn "Error near line %d, character %d\n" pos.Line pos.Column
           failwith "parser termination"


// Parse a file. (A statement is parsed) 
   let parseFromFile filename =
      if File.Exists(filename)    
      then parseString(File.ReadAllText(filename))
      else invalidArg "ParserUtil" "File not found"

open ParserUtil

open GuardedCommands.Backend
open GuardedCommands.Frontend.TypeCheck

module CompilerUtil =

/// goOpt p compiles (using the optimized version) abstract syntax of a program, runs the code  
   let goOpt p = run(code2ints(CodeGenerationOpt.CP p))
/// goOptT does the same as goOpt, but returns the runtime
   let goOptT p = runt(code2ints(CodeGenerationOpt.CP p))
/// go p compiles abstract syntax of a program, runs the code
   let go p = run(code2ints(CodeGeneration.CP p))
/// goT does the same as go, but returns the runtime
   let goT p = runt(code2ints(CodeGeneration.CP p))

/// goOpt p compiles abstract syntax of a program, runs the showing a trace  
   let goTrace p = runTrace(code2ints(CodeGeneration.CP p))
 
   let goTraceOpt p = runTrace(code2ints(CodeGenerationOpt.CP p))
    
/// exec filename parses, type checks, compiles and runs a program in a file
   let exec filename =  printfn "\nParse, typecheck, compilation and execution of %s:" filename 
                        let prog = parseFromFile filename
                        tcP prog
                        go prog

/// execOpt filename parses, type checks, compiles (using optimized version) and runs a program in a file
   let execOpt filename =  printfn "\nParse, typecheck, optimized compilation and execution of %s:" filename 
                           let prog = parseFromFile filename
                           tcP prog
                           goOpt prog
/// execT filename parses, type checks, compiles, and runs a program in a file, returning the runtime
   let execT filename =let prog = parseFromFile filename
                       tcP prog
                       goT prog
/// execOptT filename parses, type checks, compiles, and runs a program in a file, returning the runtime
   let execOptT filename = let prog = parseFromFile filename
                           tcP prog
                           goOptT prog

/// execTrace filename parses, type checks, compiles and runs a program in a file showing a program trace
   let execTrace filename =  printfn "\nParse, typecheck, compilation and execution of %s:" filename 
                             let prog = parseFromFile filename
                             tcP prog
                             goTrace prog
(*
   let exec str  = let prog = parseString str
                   Frontend.TypeCheck.tcP prog;
                   go prog *)
(*
// Parses a string. (A declaration list is parsed)  
   let parseDecList (text:string) =
      let lexbuf = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(text))
      try
          Parser.DecList Lexer.tokenize lexbuf
      with e ->
           let pos = lexbuf.EndPos
           printfn "Error near line %d, character %d\n" pos.Line pos.Column
           failwith "parser termination"

// Parses a file. (A declaration list is parsed) 
   let parseDecListFromFile filename =
     if File.Exists(filename)    
      then parseDecList(File.ReadAllText(filename))
      else invalidArg "ParserUtil" "File not found"


   let parseExp (text:string) =
      let lexbuf = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(text))
      try
          Parser.Exp Lexer.tokenize lexbuf
      with e ->
           let pos = lexbuf.EndPos
           printfn "Error near line %d, character %d\n" pos.Line pos.Column
           failwith "parser termination"


   let parseDec (text:string) =
      let lexbuf = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(text))
      try
          Parser.Dec Lexer.tokenize lexbuf
      with e ->
           let pos = lexbuf.EndPos
           printfn "Error near line %d, character %d\n" pos.Line pos.Column
           failwith "parser termination"

   let parseStm (text:string) =
      let lexbuf = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(text))
      try
          Parser.Stm Lexer.tokenize lexbuf
      with e ->
           let pos = lexbuf.EndPos
           printfn "Error near line %d, character %d\n" pos.Line pos.Column
           failwith "parser termination"

   let parseStmList (text:string) =
      let lexbuf = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(text))
      try
          Parser.StmList Lexer.tokenize lexbuf
      with e ->
           let pos = lexbuf.EndPos
           printfn "Error near line %d, character %d\n" pos.Line pos.Column
           failwith "parser termination"

   let parseProgram (text:string) =
      let lexbuf = LexBuffer<_>.FromBytes(Encoding.UTF8.GetBytes(text))
      try
          Parser.Prog Lexer.tokenize lexbuf
      with e ->
           let pos = lexbuf.EndPos
           printfn "Error near line %d, character %d\n" pos.Line pos.Column
           failwith "parser termination"

*)


(*

// Compile, type check, generate code and run a program from a file
   let goFile file = go (parseFromFile file)

   let intsFromMain(args: string[]) = 
         let file = args.[0]
         let ps = Array.map int (args.[1..]) 
         let p = parseFromFile file
         (code2ints(CP p), ps)

   let goArgsTrace (args: string[]) = 
         let (ints,ps) = intsFromMain args
         VirtualMachine.runArgsTrace ints ps 
         
   let goArgs (args: string[]) = 
         let (ints,ps) = intsFromMain args
         VirtualMachine.runArgs ints ps
  *)