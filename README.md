# babysat

Baby Steps to a SAT Solver. This solver is designed to put in practice several interesting concepts I read about regarding practical [SAT solving](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) as a **small** program, without losing too much performance. Corresponding (excellent!) resources are left as comments in source for relevant sections.

## Compilation and Execution

Use your favourite C++ compiler to compile. Sample command:

```sh
g++ main.cpp -o satsolver
```

To execute the resulting program, pass a CNF File (DIMACS format) as the first argument, e.g.:

```sh
./satsolver mycnf.cnf
```

CNF files used during development are [benchmark problems from SATLIB](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).

## Sample Performance

TODO: Plot graph
