FSLEX=mono packages/FsLexYacc.7.0.6/build/fslex.exe
FSYACC=mono packages/FsLexYacc.7.0.6/build/fsyacc.exe

all:
	$(FSLEX) Lexer.fsl
	$(FSYACC) --module Parser Parser.fsy
	dotnet build
