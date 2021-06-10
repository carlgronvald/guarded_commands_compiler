If you need to update lexer/parser, use the following commands in 
Project "Properties" -> "Build Events" -> "Prebuild event command line":

      fslex "$(ProjectDir)Lexer.fsl"
      fsyacc --module Parser "$(ProjectDir)Parser.fsy"

where fslex gives the path to the file fslex.exe, for example: 
     "$(ProjectDir)\..\packages\FsLexYacc.7.0.6\build\fslex.exe"

and fsyacc gives the path to the file fsyacc.exe, for example:
     "$(ProjectDir)\..\packages\FsLexYacc.7.0.6\build\fsyacc.exe"

Note: You must revise a path occurring in Script.fsx
