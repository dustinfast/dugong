# Dugong

A lexical analyzer, recursive descent parser, and interactive interpreter for the programming language Dugong.

The grammar for Dugong is defined in `parseit.lua` and was defined by Dr. Glenn G. Chappel. Unit tests and the REPL/Shell (`dugong.lua`) also by Dr. Chappell.

## Usage

**Dependecies:**  
Requires Lua.

**Linux Users:**  
To execute a Dugong program from source:  
`./dugong.lua DUGONG_SOURCEFILE`  

Ex: `./dugong.lua dugong_examples/fibo.du`

To start an interactive interpreter session:  
`./dugong.lua`

**Windows Users:**  
To execute a Dugong program from source:  
`lua dugong.lua DUGONG_SOURCEFILE`  

Ex: `lua dugong.lua dugong_examples/fibo.du`

To start an interactive interpreter session:  
`lua dugong.lua`
