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

assert!(engine.new_ge(&v(x), &c(5), None).is_ok());
assert!(engine.new_le(&v(x), &c(10), None).is_ok());
assert!(engine.check().is_ok());

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
5. Use `new_guard`, `assert`, and `retract` when you want constraints to be optional.
