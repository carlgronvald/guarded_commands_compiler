module Tests

open GuardedCommands.Util
open GuardedCommands.Frontend.TypeCheck
open GuardedCommands.Frontend.AST
open GuardedCommands.Backend.CodeGeneration

open ParserUtil
open CompilerUtil

let type_test file =
    parseFromFile file |> tcP

let test_with_trace file =
    let prog = parseFromFile file
    tcP prog
    goTrace prog |> ignore



let test () =
    List.iter type_test []
    List.iter test_with_trace ["Ex0.gc"]