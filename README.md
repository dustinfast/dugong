# Dugong
A lexical analyzer, recursive descent parser, and interactive interpreter for the programming lanaguge Dugong.

The grammar for Dugong is defined in `parseit.lua` and was defined by Dr. Glenn G. Chappel. Unit tests and the REPL/Shell (`dugong.lua`) also by Dr. Chappell.

## Usage
To execute a Dugong program from source, use:  
`./dugong.lua DUGONG_SOURCEFILE`  

For example:  
`./dugong.lua du_examples/testfibo.du`

Alterntively, use `./dugong.lua` to start the interactive Dugong interpreter.
