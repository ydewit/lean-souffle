# lean-souffle

A quick and dirty proof of concept to analyse LCNF using Datalog.

This repository exports all of LCNF as Souffle facts that are then
processed by Souffle using [LeanLCNF.dl](./LeanLCNF.dl).


# How to use it?

Run `make build` or manually run `lake build` and then run souffle on the generated files.
