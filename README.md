![sorg](doc/logo/logo.svg?sanitize=true)

# A Super Optimization based Rule Generator

The tool sorg takes a sequence of EVM bytecode instructions `s` and an
observationally equvivalent optimized sequence of EVM bytecode
instructions `t` and generates a rewrite rule, which can be used for
peephole optimizations.

## Example
```
$ sorg "PUSH 0 SUB PUSH 3 ADD PUSH 42" "PUSH 3 SUB PUSH 42"

PUSH 0 SUB PUSH w_3 ADD => PUSH w_3 SUB
```
