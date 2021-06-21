// Michael R. Hansen 07-06-2021

// Author: Carl Frederik Grønvald 21/06/2021, though many iterations have existed

// You must revise the following path 

#r @"packages/FsLexYacc.Runtime.7.0.6/lib/portable-net45+netcore45+wpa81+wp8+MonoAndroid10+MonoTouch10/FsLexYacc.Runtime.dll";

#load "AST.fs"
#load "Parser.fs"
#load "Lexer.fs"
#load "TypeCheck.fs"
#load "Machine.fs"
#load "CodeGen.fs"
#load "CodeGenOpt.fs"
#load "VirtualMachine.fs"
#load "Util.fs"


open GuardedCommands.Util
open GuardedCommands.Frontend.TypeCheck
open GuardedCommands.Frontend.AST
open GuardedCommands.Backend.CodeGeneration

open ParserUtil
open CompilerUtil



System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

parseFromFile "chartest.gc"
tcP (parseFromFile "chartest.gc")
execOpt "chartest.gc"

List.iter execOpt ["Ex0.gc";"Ex1.gc";"Ex2.gc";"Ex3.gc"]
List.iter execOpt ["Ex4.gc";"Ex5.gc";"Ex6.gc";"Ex7.gc"]
goTraceOpt (parseFromFile "Ex7.gc")

List.iter execOpt ["fact.gc"; "factCBV.gc"; "factRec.gc"]

List.iter execOpt ["QuickSortV1.gc"; "QuickSortV2.gc"; "factImpPTyp.gc"]
execOpt "par1.gc"

execOpt "Test_functions.gc"

execOpt "QuickSortV2.gc"



(* Testing functions and procedures *)

let testTree = parseFromFile  "A0.gc";;
printfn "%A" testTree
let code = CP testTree
printfn "%A" code





let ex0Tree = parseFromFile "Ex0.gc";;

let _ = tcP ex0Tree;;

let ex0Code = CP ex0Tree;; 

let _ = go ex0Tree;;

let _ = goTrace ex0Tree;;


// Parsing of Ex1.gc

let ex1Tree = parseFromFile "Ex1.gc";; 

// -- is typechecked as follows:

let _ = tcP ex1Tree;;

// obtain symbolic code:
let ex1Code = CP ex1Tree;; 

// -- is executed with trace as follows:
let stack = goTrace ex1Tree;;

// -- is executed as follows (no trace):
let sameStack = go ex1Tree;;

// "All in one" parse from file, type check, compile and run 

let _ = exec "Ex1.gc";;

let _ = exec "Ex2.gc";;


// All programs relating to the basic version can be parsed:
let pts = List.map parseFromFile ["Ex1.gc"; "Ex2.gc";"Ex3.gc"; "Ex4.gc"; "Ex5.gc"; "Ex6.gc"; "Skip.gc"];;

// The parse tree for Ex3.gc
List.item 2 pts ;;


// Test of programs covered by the first task (Section 3.7):
List.iter exec ["Ex1.gc"; "Ex2.gc";"Ex3.gc"; "Ex4.gc"; "Ex5.gc"; "Ex6.gc"; "Skip.gc"];;

// Test of programs covered by the second task (Section 4.3):
List.iter exec ["Ex7.gc"; "fact.gc"; "factRec.gc"; "factCBV.gc"];;

// Test of programs covered by the fourth task (Section 5.4):
goTrace (parseFromFile "A0.gc")
List.iter exec ["A0.gc"; "A1.gc"; "A2.gc"; "A3.gc"];;

// Test of programs covered by the fifth task (Section 6.1):
List.iter exec ["Swap.gc"; "QuickSortV1.gc"];;

// Test of programs covered by the fifth task (Section 7.4):
List.iter exec ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"];;

// Test of programs covered by the fifth task using optimized compilation (Section 8.2):
List.iter execOpt ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"];;

// Our own tests
List.iter execOpt ["chartest.gc"; "function_test.gc"; "function_test_2.gc"; "Test_functions.gc"; "Ex11.gc"; "Exa1.gc"];;

// More of our tests
List.iter execOpt ["arr_test.gc"; "cond_test.gc"; "div_test.gc"; "do_od_test.gc"; "ge_test.gc"; "if_fi_test.gc"; "mass_test.gc"];;

// Time unoptimized and optimized code
let comp_time filename =
    let total_opt_time = seq {for i in 1..10 do execOptT filename} |> Seq.sum
    let total_unopt_time = seq {for i in 1..10 do execT filename} |> Seq.sum
    
    printfn "Total opt time %A, total unopt time %A" total_opt_time total_unopt_time
    
comp_time "QuickSortV2.gc"
comp_time "QuickSortV1.gc"
comp_time "Ex11_no_output.gc"
comp_time "Ex7.gc"


