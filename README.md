# Surreal Numbers in Coq/Rocq

A formalization of John H. Conway's surreal numbers in Rocq (formerly Coq), based on Knuth's "Surreal Numbers: How Two Ex-Students Turned On to Pure Mathematics and Found Total Happiness."

## Overview

Surreal numbers are a class of numbers that includes all real numbers as well as infinite and infinitesimal numbers. They are constructed recursively:
- A surreal number $x = \{L \mid R\}$ consists of a left set $L$ and right set $R$ of previously created surreal numbers
- Every element of $L$ is less than every element of $R$
- The ordering $x \leq y$ holds when no element of $x$'s left set is $\leq y$ and no element of $y$'s right set is $\geq x$

## Project Structure

| File | Description |
|------|-------------|
| `base.v` | Core definitions: surreal numbers, ordering relations ($\leq$, $\ngeq$), basic lemmas |
| `equiv.v` | Equivalence relations and set-level equality between surreal numbers |
| `add.v` | Addition, negation, subtraction, and their algebraic properties |
| `add_facts.v` | Additional algebraic facts and theorems about operations |
| `pseudo.v` | Pseudo-number examples and classical results |
| `exercises.v` | Solutions to exercises from the book |

## Building

Requires Rocq (Coq) 9.1 or later.

```bash
# Generate Makefile
rocq makefile -f _RocqProject -o Makefile

# Build all modules
make

# Build a specific file
make base.vo

# Validate compiled artifacts
make validate

# Generate documentation
make html

# Clean build artifacts
make clean
```

## Quick Start

Interactive exploration with the Rocq REPL:

```bash
rocq repl -Q . SN
```

Example session:
```coq
From SN Require Import base.
Check sle_refl.
```

## Key Definitions

- **Surreal numbers**: Inductive type `surreal` with constructor `snlr` for left/right sets
- **Ordering**: Mutual inductive definitions `sle` ($\leq$) and `snge` ($\ngeq$)
- **Notation**: `[l, r]` constructs a surreal number from left map `l` and right map `r`

## References

- Donald E. Knuth. *Surreal Numbers: How Two Ex-Students Turned On to Pure Mathematics and Found Total Happiness*. Addison-Wesley, 1974.
- John H. Conway. *On Numbers and Games*. A K Peters, 2000.

## License

See repository for licensing information.
