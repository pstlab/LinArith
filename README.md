# LinArith

[![Rust](https://img.shields.io/badge/Rust-1.95+-orange?logo=rust)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/License-MIT-green)](LICENSE)
![Build Status](https://github.com/pstlab/LinArith/actions/workflows/rust.yml/badge.svg)
[![codecov](https://codecov.io/gh/pstlab/LinArith/branch/main/graph/badge.svg)](https://codecov.io/gh/pstlab/LinArith)

LinArith is an incremental linear feasibility solver over rational numbers.

It is designed for maintaining and propagating linear constraints of the form
`lhs <= rhs`, `lhs < rhs`, `lhs == rhs`, `lhs >= rhs`, and `lhs > rhs` over
variables, rational numbers, and infinitesimal bounds.

## Quick Start

```rust
use linarith::{c, v, Engine};

let mut engine = Engine::new();
let x = engine.add_var();

// Add constraints: 5 <= x <= 10
engine.new_ge(&v(x), &c(5), None).expect("constraint should be consistent");  // x >= 5
engine.new_le(&v(x), &c(10), None).expect("constraint should be consistent"); // x <= 10
engine.check().expect("feasibility check should succeed");

// Verify the solver computed bounds correctly
assert!(engine.val(x) >= &linarith::i_rat(linarith::r(5)));
assert!(engine.val(x) <= &linarith::i_rat(linarith::r(10)));
```

## Core Concepts

- `Engine` stores variable assignments, bounds, and the tableau used for propagation.
- `VarId` identifies variables created by the solver.
- `GuardId` lets you group bounds into named constraints that can be asserted and retracted.
- `Lin`, `Rational`, and `InfRational` are the building blocks for linear expressions and bounds.

## Typical Workflow

1. Create an `Engine`.
2. Add variables with `add_var` or `add_lin_var`.
3. Add constraints with `new_le`, `new_lt`, `new_eq`, `new_ge`, or `new_gt`.
4. Call `check` to restore feasibility when needed.
5. Use `add_guard`, `assert`, and `retract` when you want constraints to be optional.

## Non-chronological Constraint Retraction

One of the core features of LinArith is **non-chronological retraction**: you can remove
constraints in any order, not just in reverse order of addition.

This is achieved through the guard system:

```rust
let mut engine = Engine::new();
let x = engine.add_var();
let y = engine.add_var();

let g1 = engine.add_guard();
let g2 = engine.add_guard();

// Add and assert constraints in order: g1 first, then g2
engine.new_ge(&v(x), &c(5), Some(g1)).expect("constraint should be consistent"); // x >= 5 (under g1)
engine.assert(g1).expect("guard assertion should succeed");                      // Assert g1 [1st]

engine.new_le(&v(y), &c(10), Some(g2)).expect("constraint should be consistent"); // y <= 10 (under g2)
engine.assert(g2).expect("guard assertion should succeed");                       // Assert g2 [2nd]

// Key point: retract the FIRST constraint (g1), leaving g2 active
// In a chronological (stack-like) system this would be impossible!
// You'd have to retract g2 first, then g1. Not here.
engine.retract(g1);  // Retract the FIRST asserted constraint, even though g2 came after!

// g1's constraint is gone, but g2's remains
assert_eq!(engine.lb(x), &InfRational::NEGATIVE_INFINITY); // x is unbounded
assert_eq!(engine.ub(y), &i_rat(r(10)));                   // y <= 10 still active!
```

The solver maintains an efficient dual-index system:
- Each variable tracks which guards set each of its bounds
- Each guard tracks which variables it constrains

This enables O(1) cleanup when retracting, making backtracking and hypothetical reasoning efficient.
