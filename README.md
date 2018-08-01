# Dugong
A lexical analyzer, recursive descent parser, and interactive interpreter for the programming language Dugong.

The grammar for Dugong is defined in `parseit.lua` and was defined by Dr. Glenn G. Chappel. Unit tests and the REPL/Shell (`dugong.lua`) also by Dr. Chappell.

## Usage
**Dependecies:**  
Requires Lua.

**Linux Users:**
To execute a Dugong program from source, use:  
`./dugong.lua DUGONG_SOURCEFILE`  

For example:  
`./dugong.lua dugong_examples/fibo.du`

Alterntively, use `./dugong.lua` to start the interactive Dugong interpreter.

**Windows Users:**  
On windows, the `./` in the above Linux commands must be replaced with `lua`. For example:  

`./dugong.lua dugong_examples/fibo.du`
  
Becomes

`lua dugong.lua dugong_examples/fibo.du`
