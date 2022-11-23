# lean-souffle

A quick and dirty proof of concept to perform static analysis on Lean4 AST's using Souffle, a Datalog engine.

The integration is quite simple: we simply export Lean4´s internal ASTs into a set of file-based facts, one for each relation. And
this is done for `Lean.Expr`, namespaces, modules and module imports, and `Lean.Compiler.LCNF.Decl`.

## How to use it?

Building this repo with Lake will generate `.facts` files in the `./facts/` folder. Each file contains all the facts for one relation.
The compilation will also generate declarations for the all relations exported in a single file: [./dl/Lean.dl](./dl/Lean.dl). This
file can be included to create Datalog queries and rules.

The included [Makefile](./Makefile) will setup all the paths to run Souffle on the generated files. Simply run `make` to get all relations
exported and run one of the analysis on it. The output relations are saved in `./build/outputs/`.

## An incomplete list of TODOs

* [X] Export `Lean.Compiler.LCNF.Decl`
* [X] Export modules and module imports
* [X] Export `Lean.Expr`
* [X] Export namespaces
* [ ] Use first class support sums and records in Souffle
* [ ] Emit `Level` from  `Expr`'s
* [ ] Emit `KVMap`'s `DataValue`
