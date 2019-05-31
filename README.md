![sorg](doc/logo/logo.svg?sanitize=true)

# A Super Optimization based Rule Generator

The tool sorg takes a sequence of EVM bytecode instructions `s` and an
observationally equvivalent optimized sequence of EVM bytecode
instructions `t` and generates a rewrite rule, which can be used in
peephole optimizations.

The tool sorg is based on optimizations the tool ebso finds
optimizations for loop-free Ethereum bytecode.

## Example
```
$ ./sorg -s "PUSH 0 SUB PUSH 3 ADD PUSH 42" -t "PUSH 3 SUB PUSH 42"
The rule

PUSH 0 SUB PUSH $x$ ADD -> PUSH $x$ SUB

is generated from this optimization. 

Applying the rule saves 6 gas and 2 instructions.
```
