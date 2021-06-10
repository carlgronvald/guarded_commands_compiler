// A simplified fsharp program closely based on a the programs 
// machine.c and Machine.java from the MicroC compiler by  Peter Sestoft

// Michael R. Hansen 07-06-2021
module VirtualMachine

let CODECSTI   = 0 
let CODEADD    = 1 
let CODESUB    = 2 
let CODEMUL    = 3 
let CODEDIV    = 4 
let CODEMOD    = 5 
let CODEEQ     = 6 
let CODELT     = 7 
let CODENOT    = 8 
let CODEDUP    = 9 
let CODESWAP   = 10 
let CODELDI    = 11 
let CODESTI    = 12 
let CODEGETBP  = 13 
let CODEGETSP  = 14 
let CODEINCSP  = 15 
let CODEGOTO   = 16
let CODEIFZERO = 17
let CODEIFNZRO = 18 
let CODECALL   = 19
let CODETCALL  = 20
let CODERET    = 21
let CODEPRINTI = 22 
let CODEPRINTC = 23
let CODELDARGS = 24
let CODESTOP   = 25


let STACKSIZE = 10000

let insname(p: int[], pc: int) =
   match p.[pc] with
   | i when i=CODECSTI   -> "CSTI " + string p.[pc+1] 
   | i when i=CODEADD    -> "ADD"
   | i when i=CODESUB    -> "SUB"
   | i when i=CODEMUL    -> "MUL"
   | i when i=CODEDIV    -> "DIV"
   | i when i=CODEMOD    -> "MOD"
   | i when i=CODEEQ     -> "EQ"
   | i when i=CODELT     -> "LT"
   | i when i=CODENOT    -> "NOT"
   | i when i=CODEDUP    -> "DUP"
   | i when i=CODESWAP   -> "SWAP"
   | i when i=CODELDI    -> "LDI"
   | i when i=CODESTI    -> "STI"
   | i when i=CODEGETBP  -> "GETBP"
   | i when i=CODEGETSP  -> "GETSP"
   | i when i=CODEINCSP  -> "INCSP " + string  p.[pc+1]
   | i when i=CODEGOTO   -> "GOTO " + string p.[pc+1]
   | i when i=CODEIFZERO -> "IFZERO " + string p.[pc+1]
   | i when i=CODEIFNZRO -> "IFNZRO " + string p.[pc+1]
   | i when i=CODECALL   -> "CALL " + string p.[pc+1] + " " + string p.[pc+2]
   | i when i=CODETCALL  -> "TCALL " + string p.[pc+1] + " " + string p.[pc+2] + " " + string p.[pc+3]
   | i when i=CODERET    -> "RET " + (string p.[pc+1])
   | i when i=CODEPRINTI -> "PRINTI"
   | i when i=CODEPRINTC -> "PRINTC"
   | i when i=CODELDARGS -> "LDARGS"
   | i when i=CODESTOP   -> "STOP"
   | _                   -> "<unknown>"
   
let  printsppc(s: int[], bp, sp, p, pc) =
    System.Console.Write("[ ")
    let i = ref 0
    while !i <=sp do
      System.Console.Write(string s.[!i] + " "); i := !i + 1
    System.Console.Write("]")
    System.Console.WriteLine("{" + string pc + ": " + insname(p, pc) + "}");  

let rec execcode(p: int[], s: int[], iargs: int[]) trace = 
  let bp = ref -999 
  let sp = ref -1
  let pc = ref 0 
  let execStep i = 
    match i with
    | i when i=CODECSTI   -> s.[!sp+1] <- p.[!pc+1]; sp := !sp+1; pc := !pc+2
    | i when i=CODEADD    -> s.[!sp-1] <- s.[!sp-1] + s.[!sp]; sp := !sp-1; pc := !pc+1
    | i when i=CODESUB    -> s.[!sp-1] <- s.[!sp-1] - s.[!sp]; sp := !sp-1; pc := !pc+1
    | i when i=CODEMUL    -> s.[!sp-1] <- s.[!sp-1] * s.[!sp]; sp := !sp-1; pc := !pc+1
    | i when i=CODEDIV    -> s.[!sp-1] <- s.[!sp-1] / s.[!sp]; sp := !sp-1; pc := !pc+1
    | i when i=CODEMOD    -> s.[!sp-1] <- s.[!sp-1] % s.[!sp]; sp := !sp-1; pc := !pc+1
    | i when i=CODEEQ     -> s.[!sp-1] <- (if s.[!sp-1] = s.[!sp] then 1 else 0); sp := !sp-1; pc := !pc+1
    | i when i=CODELT     -> s.[!sp-1] <- (if s.[!sp-1] < s.[!sp] then 1 else 0); sp := !sp-1; pc := !pc+1
    | i when i=CODENOT    -> (s.[!sp] <- if s.[!sp] = 0 then 1 else 0); pc := !pc+1
    | i when i=CODEDUP    -> s.[!sp+1] <- s.[!sp]; sp := !sp+1; pc := !pc+1
    | i when i=CODESWAP   -> let tmp = s.[!sp]  
                             s.[!sp] <- s.[!sp-1];  s.[!sp-1] <- tmp; pc := !pc+1 
    | i when i=CODELDI    -> s.[!sp] <- s.[s.[!sp]]; pc := !pc+1                                  // load indirect        
    | i when i=CODESTI    -> s.[s.[!sp-1]] <- s.[!sp]; s.[!sp-1] <- s.[!sp]; sp := !sp-1; pc := !pc+1 // store indirect, keep value on top
    | i when i=CODEGETBP  -> s.[!sp+1] <- !bp; sp := !sp+1; pc := !pc+1
    | i when i=CODEGETSP  -> s.[!sp+1] <- !sp; sp := !sp+1; pc := !pc+1
    | i when i=CODEINCSP  -> sp := !sp+p.[!pc+1]; pc := !pc+2
    | i when i=CODEGOTO   -> pc := p.[!pc+1]
    | i when i=CODEIFZERO -> (pc := if s.[!sp] = 0 then p.[!pc+1] else !pc+2); sp := !sp-1
    | i when i=CODEIFNZRO -> (pc := if s.[!sp] <> 0 then p.[!pc+1] else !pc+2); sp := !sp-1     
    | i when i=CODECALL   -> 
        let argc = p.[!pc+1]
        let k = ref 0
        while !k<argc do                             // Make room for return address
          s.[!sp - !k+2] <- s.[!sp - !k]; k := !k+1  // and old base pointer
        s.[!sp-argc+1] <- !pc+3; sp := !sp+1 
        s.[!sp-argc+1] <- !bp; sp := !sp+1  
        bp := !sp+1-argc
        pc := p.[!pc+2] 
    | i when i=CODETCALL  -> 
        let argc = p.[!pc+1]                // Number of new arguments
        let pop  = p.[!pc+2]               // Number of variables to discard
        let k = ref (argc-1)
        while !k>=0 do                    // Discard variables
          s.[!sp - !k - pop] <- s.[!sp - !k]; k := !k-1 
        sp := !sp - pop; pc := p.[!pc+3] 
    | i when i=CODERET    -> 
        let res = s.[!sp] 
        sp := !sp-p.[!pc+1]; bp := s.[!sp-1]; pc := s.[!sp-2];  sp := !sp-2 
        s.[!sp] <- res            
    | i when i=CODEPRINTI -> System.Console.WriteLine(string s.[!sp] + " ") ; pc := !pc+1  
    | i when i=CODEPRINTC -> System.Console.WriteLine((char)(s.[!sp])); pc := !pc+1 
    | i when i=CODELDARGS -> let k = ref 0
                             while !k< iargs.Length do  // Push commandline arguments
                                sp:= !sp+1; s.[!sp] <- iargs.[!k] ; k:= !k + 1 
                             pc := !pc + 1
    | _                   ->  failwith("Illegal instruction " + string p.[!pc] + " at address " + string !pc)


  let rec exec() = let i = p.[!pc]
                   if trace then printsppc(s, !bp, !sp, p, !pc) 
                   if i = CODESTOP then s.[0..!sp]
                   else ((execStep i) ; exec())
  exec()

let runArgs is iargs = let p = Array.ofList is
                       let s = Array.init STACKSIZE (fun _ -> 0)
                       execcode(p,s,iargs) false

let runArgsTrace is iargs= let p = Array.ofList is
                           let s = Array.init STACKSIZE (fun _ -> 0)
                           execcode(p,s,iargs) true


let run is = let sw = new System.Diagnostics.Stopwatch()
             let _  = sw.Start()
             let stk = runArgs is [||]
             let elabsed = int sw.ElapsedMilliseconds
             printfn "\nStack : %s" (Array.fold (fun s n -> s + (string n) + "  ") "" stk)
             printfn "\nRan %d miliseconds" elabsed
              
let runTrace is = runArgsTrace is [||]




 