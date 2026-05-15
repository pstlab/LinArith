//! LinArith is an incremental linear feasibility solver over rational numbers.
//!
//! The crate lets you maintain linear constraints over variables and keeps the
//! current assignments feasible by propagating bound changes through a tableau.
//! Constraints can be asserted immediately or collected under a guard and
//! activated later.
//!
//! ## Example
//!
//! ```rust
//! use linarith::{v, Engine, Lin};
//!
//! let mut engine = Engine::new();
//! let x = engine.add_var();
//!
//! assert!(engine.new_ge(&v(x), &Lin::from(5), None).is_ok());
//! assert!(engine.new_le(&v(x), &Lin::from(10), None).is_ok());
//! assert!(engine.check().is_ok());
//! ```

mod inf_rational;
mod lin;
mod rational;
mod var;

pub use inf_rational::{InfRational, inf, inf_i};
pub use lin::{Lin, v, vc};
pub use rational::Rational;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt, mem,
};
pub use var::VarId;

type Callback = Box<dyn Fn(VarId, &InfRational, &InfRational, &InfRational)>; // Callback type for variable changes: (variable index, new value, new lower bound, new upper bound)

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GuardId(usize);

struct GuardBounds {
    lbs: HashMap<VarId, InfRational>, // variables' lower bounds set by this constraint
    ubs: HashMap<VarId, InfRational>, // variables' upper bounds set by this constraint
}

impl GuardBounds {
    fn new() -> Self {
        GuardBounds { lbs: HashMap::new(), ubs: HashMap::new() }
    }

    fn set_lb(&mut self, var: VarId, lb: InfRational) {
        if let Some(c_lb) = self.lbs.get(&var) {
            if c_lb < &lb {
                self.lbs.insert(var, lb);
            }
        } else {
            self.lbs.insert(var, lb);
        }
    }

    fn set_ub(&mut self, var: VarId, ub: InfRational) {
        if let Some(c_ub) = self.ubs.get(&var) {
            if c_ub > &ub {
                self.ubs.insert(var, ub);
            }
        } else {
            self.ubs.insert(var, ub);
        }
    }
}

pub struct Engine {
    assignments: Vec<InfRational>,                     // the current variable assignments
    lbs: Vec<BTreeMap<InfRational, HashSet<GuardId>>>, // lower bounds for each variable, mapping from bound to the set of constraints that set it
    ubs: Vec<BTreeMap<InfRational, HashSet<GuardId>>>, // upper bounds for each variable, mapping from bound to the set of constraints that set it
    guard_bounds: Vec<GuardBounds>,                    // list of constraints, each containing the bounds it sets on variables
    tableau: BTreeMap<VarId, Lin>,                     // the tableau, mapping basic variable indices to their corresponding linear expressions
    t_watches: Vec<HashSet<VarId>>,                    // for each variable, the set of tableau rows that watch it (i.e., contain it in their expression)
    listeners: HashMap<VarId, Vec<Callback>>,          // listeners for variable changes, indexed by variable index
}

/// An error returned when constraint propagation detects an inconsistency.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropagationError {
    /// The solver found a contradiction. The contained list identifies the
    /// [`GuardId`]s whose bounds jointly caused the conflict.
    Conflict(Vec<GuardId>),
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    /// Creates an empty solver instance.
    pub fn new() -> Self {
        Engine {
            assignments: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            guard_bounds: Vec::new(),
            tableau: BTreeMap::new(),
            t_watches: Vec::new(),
            listeners: HashMap::new(),
        }
    }

    /// Adds a fresh unconstrained variable and returns its identifier.
    pub fn add_var(&mut self) -> VarId {
        let index = self.assignments.len();
        self.assignments.push(InfRational::ZERO);
        self.lbs.push(BTreeMap::new());
        self.ubs.push(BTreeMap::new());
        self.t_watches.push(HashSet::new());
        VarId(index)
    }

    /// Adds a fresh variable whose initial value is the value of `lin`.
    ///
    /// The linear expression is stored in the tableau as the definition of the
    /// new basic variable.
    pub fn add_lin_var(&mut self, lin: Lin) -> VarId {
        let index = self.add_var();
        self.assignments[index.0] = self.lin_val(&lin);
        self.new_row(index, lin);
        index
    }

    /// Adds a new guard used to group constraints for later assertion or retraction.
    pub fn add_guard(&mut self) -> GuardId {
        let index = self.guard_bounds.len();
        self.guard_bounds.push(GuardBounds::new());
        GuardId(index)
    }

    /// Returns the current assignment of `var`.
    pub fn val(&self, var: VarId) -> &InfRational {
        &self.assignments[var.0]
    }

    /// Returns the tightest active lower bound of `var`,
    /// or [`InfRational::NEGATIVE_INFINITY`] if none has been set.
    pub fn lb(&self, var: VarId) -> &InfRational {
        self.lbs[var.0].iter().next_back().map(|(lb, _)| lb).unwrap_or(&InfRational::NEGATIVE_INFINITY)
    }

    /// Returns the tightest active upper bound of `var`,
    /// or [`InfRational::POSITIVE_INFINITY`] if none has been set.
    pub fn ub(&self, var: VarId) -> &InfRational {
        self.ubs[var.0].iter().next().map(|(ub, _)| ub).unwrap_or(&InfRational::POSITIVE_INFINITY)
    }

    /// Evaluates a linear expression under the current variable assignments.
    pub fn lin_val(&self, lin: &Lin) -> InfRational {
        let mut result = InfRational::from(lin.known_term);
        for (&var, &coeff) in &lin.vars {
            result += coeff * self.val(var);
        }
        result
    }

    /// Computes the tightest lower bound of a linear expression given the
    /// current variable bounds.
    pub fn lin_lb(&self, lin: &Lin) -> InfRational {
        let mut result = InfRational::from(lin.known_term);
        for (&var, &coeff) in &lin.vars {
            if coeff.is_positive() {
                result += coeff * self.lb(var);
            } else {
                result += coeff * self.ub(var);
            }
        }
        result
    }

    /// Computes the tightest upper bound of a linear expression given the
    /// current variable bounds.
    pub fn lin_ub(&self, lin: &Lin) -> InfRational {
        let mut result = InfRational::from(lin.known_term);
        for (&var, &coeff) in &lin.vars {
            if coeff.is_positive() {
                result += coeff * self.ub(var);
            } else {
                result += coeff * self.lb(var);
            }
        }
        result
    }

    /// Returns `true` when the current bounds of `lhs` and `rhs` overlap.
    pub fn overlap(&self, lhs: VarId, rhs: VarId) -> bool {
        self.lb(lhs) < self.ub(rhs) && self.lb(rhs) < self.ub(lhs)
    }

    /// Asserts that `var >= lb`, attributed to the optional `guard` constraint.
    ///
    /// If the new lower bound exceeds the current upper bound, a
    /// [`PropagationError::Conflict`] is returned immediately without modifying
    /// state. Otherwise the bound is recorded and, if the non-basic variable's
    /// current value falls below `lb`, its assignment is updated accordingly.
    ///
    /// # Panics
    /// Panics if `lb` is negative infinity.
    pub fn set_lb(&mut self, var: VarId, lb: InfRational, guard: Option<GuardId>) -> Result<(), PropagationError> {
        assert!(lb > InfRational::NEGATIVE_INFINITY, "Lower bound cannot be negative infinity");
        if &lb > self.ub(var) {
            let mut conflict = Vec::new();
            if let Some(guard) = guard {
                conflict.push(guard);
            }
            for guard in self.ubs[var.0].iter().next().unwrap().1.iter() {
                conflict.push(*guard);
            }
            return Err(PropagationError::Conflict(conflict)); // Inconsistent constraint
        }

        if let Some(guard) = guard {
            // When tightening (increasing) a bound via the same guard, the old bound entry
            // is cleaned up (removed if empty) and the new one is recorded.
            // Check if this guard already has a lower bound for this variable
            if let Some(c_lb) = self.guard_bounds[guard.0].lbs.get(&var) {
                // Only update if the new bound is tighter (larger)
                if *c_lb < lb {
                    // Remove the guard from the old bound entry, and delete the entry if it becomes empty
                    if self.lbs[var.0].get_mut(c_lb).is_some_and(|guards| {
                        guards.remove(&guard);
                        guards.is_empty()
                    }) {
                        self.lbs[var.0].remove(c_lb);
                    }
                    // Add the guard to the new (tighter) bound entry
                    self.lbs[var.0].entry(lb).or_default().insert(guard);
                }
            } else {
                // First time setting a lower bound for this (guard, var) pair
                self.lbs[var.0].entry(lb).or_default().insert(guard);
            }
            // Update the guard's internal record
            self.guard_bounds[guard.0].set_lb(var, lb);
        } else {
            // Guard-less constraint: just ensure the entry exists for consistency
            self.lbs[var.0].entry(lb).or_default();
        }

        if self.val(var) < &lb && !self.is_basic(var) {
            self.update(var, lb);
        }

        Ok(())
    }

    /// Asserts that `var <= ub`, attributed to the optional `guard` constraint.
    ///
    /// If the new upper bound falls below the current lower bound, a
    /// [`PropagationError::Conflict`] is returned immediately without modifying
    /// state. Otherwise the bound is recorded and, if the non-basic variable's
    /// current value exceeds `ub`, its assignment is updated accordingly.
    ///
    /// # Panics
    /// Panics if `ub` is positive infinity.
    pub fn set_ub(&mut self, var: VarId, ub: InfRational, guard: Option<GuardId>) -> Result<(), PropagationError> {
        assert!(ub < InfRational::POSITIVE_INFINITY, "Upper bound cannot be positive infinity");
        if &ub < self.lb(var) {
            let mut conflict = Vec::new();
            if let Some(guard) = guard {
                conflict.push(guard);
            }
            for guard in self.lbs[var.0].iter().next_back().unwrap().1.iter() {
                conflict.push(*guard);
            }
            return Err(PropagationError::Conflict(conflict)); // Inconsistent constraint
        }

        if let Some(guard) = guard {
            // When tightening (decreasing) a bound via the same guard, the old bound entry
            // is cleaned up (removed if empty) and the new one is recorded.
            // Check if this guard already has an upper bound for this variable
            if let Some(c_ub) = self.guard_bounds[guard.0].ubs.get(&var) {
                // Only update if the new bound is tighter (smaller)
                if *c_ub > ub {
                    // Remove the guard from the old bound entry, and delete the entry if it becomes empty
                    if self.ubs[var.0].get_mut(c_ub).is_some_and(|guards| {
                        guards.remove(&guard);
                        guards.is_empty()
                    }) {
                        self.ubs[var.0].remove(c_ub);
                    }
                    // Add the guard to the new (tighter) bound entry
                    self.ubs[var.0].entry(ub).or_default().insert(guard);
                }
            } else {
                // First time setting an upper bound for this (guard, var) pair
                self.ubs[var.0].entry(ub).or_default().insert(guard);
            }
            // Update the guard's internal record
            self.guard_bounds[guard.0].set_ub(var, ub);
        } else {
            // Guard-less constraint: just ensure the entry exists for consistency
            self.ubs[var.0].entry(ub).or_default();
        }

        if self.val(var) > &ub && !self.is_basic(var) {
            self.update(var, ub);
        }

        Ok(())
    }

    /// Adds a strict or non-strict upper-bound constraint `lhs < rhs` or `lhs <= rhs`.
    ///
    /// If the constraint is satisfiable immediately, the corresponding bound is
    /// recorded. Otherwise a conflict is returned.
    pub fn new_lt(&mut self, lhs: &Lin, rhs: &Lin, strict: bool, guard: Option<GuardId>) -> Result<(), PropagationError> {
        let mut expr = lhs - rhs;
        // Remove basic variables from the expression and substitute with their tableau expressions
        for v in expr.vars.keys().cloned().collect::<Vec<VarId>>() {
            if let Some(row) = self.tableau.get(&v) {
                expr.substitute(v, row);
            }
        }

        match expr.vars.len() {
            0 => {
                // If the expression is constant, check if it satisfies the constraint
                if if strict { expr.known_term.is_negative() } else { !expr.known_term.is_positive() } { Ok(()) } else { Err(PropagationError::Conflict(vec![])) }
            }
            1 => {
                // If the expression has one variable, we can directly set a bound on it
                let (&var, &coeff) = expr.vars.iter().next().unwrap();
                let val = inf(-expr.known_term / coeff, if strict { if coeff.is_positive() { Rational::from(-1) } else { Rational::from(1) } } else { Rational::ZERO });

                if coeff.is_positive() {
                    if let Some(guard) = guard {
                        self.guard_bounds[guard.0].set_ub(var, val);
                        Ok(())
                    } else {
                        self.set_ub(var, val, guard)
                    }
                } else {
                    if let Some(guard) = guard {
                        self.guard_bounds[guard.0].set_lb(var, val);
                        Ok(())
                    } else {
                        self.set_lb(var, val, guard)
                    }
                }
            }
            _ => {
                // If the expression has multiple variables, we introduce a new slack variable and set a bound on it
                let val = inf(-mem::take(&mut expr.known_term), if strict { Rational::from(-1) } else { Rational::ZERO });
                let slack = self.add_lin_var(expr);
                if let Some(guard) = guard {
                    self.guard_bounds[guard.0].set_ub(slack, val);
                    Ok(())
                } else {
                    self.set_ub(slack, val, guard)
                }
            }
        }
    }

    /// Adds the constraint `lhs <= rhs`.
    pub fn new_le(&mut self, lhs: &Lin, rhs: &Lin, guard: Option<GuardId>) -> Result<(), PropagationError> {
        self.new_lt(lhs, rhs, false, guard)
    }

    /// Adds the constraint `lhs == rhs`.
    pub fn new_eq(&mut self, lhs: &Lin, rhs: &Lin, guard: Option<GuardId>) -> Result<(), PropagationError> {
        let mut expr = lhs - rhs;
        // Remove basic variables from the expression and substitute with their tableau expressions
        for v in expr.vars.keys().cloned().collect::<Vec<VarId>>() {
            if let Some(row) = self.tableau.get(&v) {
                expr.substitute(v, row);
            }
        }

        match expr.vars.len() {
            0 => {
                // If the expression is constant, check if it satisfies the constraint
                if expr.known_term.is_zero() { Ok(()) } else { Err(PropagationError::Conflict(vec![])) }
            }
            1 => {
                // If the expression has one variable, we can directly set a bound on it
                let (&var, &coeff) = expr.vars.iter().next().unwrap();
                let val = InfRational::from(-expr.known_term / coeff);
                if coeff.is_positive() {
                    if let Some(guard) = guard {
                        self.guard_bounds[guard.0].set_lb(var, val);
                        self.guard_bounds[guard.0].set_ub(var, val);
                        Ok(())
                    } else {
                        self.set_lb(var, val, guard)?;
                        self.set_ub(var, val, guard)
                    }
                } else {
                    if let Some(guard) = guard {
                        self.guard_bounds[guard.0].set_lb(var, val);
                        self.guard_bounds[guard.0].set_ub(var, val);
                        Ok(())
                    } else {
                        self.set_ub(var, val, guard)?;
                        self.set_lb(var, val, guard)
                    }
                }
            }
            _ => {
                // If the expression has multiple variables, we introduce a new slack variable and set bounds on it
                let val = InfRational::from(-mem::take(&mut expr.known_term));
                let slack = self.add_lin_var(expr);
                if let Some(guard) = guard {
                    self.guard_bounds[guard.0].set_lb(slack, val);
                    self.guard_bounds[guard.0].set_ub(slack, val);
                    Ok(())
                } else {
                    self.set_lb(slack, val, guard)?;
                    self.set_ub(slack, val, guard)
                }
            }
        }
    }

    /// Adds the constraint `lhs >= rhs`.
    pub fn new_ge(&mut self, lhs: &Lin, rhs: &Lin, guard: Option<GuardId>) -> Result<(), PropagationError> {
        self.new_lt(rhs, lhs, false, guard)
    }

    /// Adds a strict or non-strict lower-bound constraint `lhs > rhs` or `lhs >= rhs`.
    pub fn new_gt(&mut self, lhs: &Lin, rhs: &Lin, strict: bool, guard: Option<GuardId>) -> Result<(), PropagationError> {
        self.new_lt(rhs, lhs, strict, guard)
    }

    /// Activates all bounds registered under `constraint`.
    ///
    /// Each lower/upper bound stored in the constraint is applied via
    /// [`set_lb`](Self::set_lb) / [`set_ub`](Self::set_ub). On the first
    /// conflict the constraint is automatically retracted and the error is
    /// returned.
    pub fn assert(&mut self, constraint: GuardId) -> Result<(), PropagationError> {
        // Add the constraint's bounds to the engine
        for (var, val) in mem::take(&mut self.guard_bounds[constraint.0].lbs) {
            if let Err(e) = self.set_lb(var, val, Some(constraint)) {
                self.retract(constraint);
                return Err(e);
            }
        }
        for (var, val) in mem::take(&mut self.guard_bounds[constraint.0].ubs) {
            if let Err(e) = self.set_ub(var, val, Some(constraint)) {
                self.retract(constraint);
                return Err(e);
            }
        }
        Ok(())
    }

    /// Removes all bounds that were asserted by `constraint`.
    ///
    /// After retracting, those bounds no longer participate in conflict
    /// detection or bound propagation.
    pub fn retract(&mut self, constraint: GuardId) {
        // Remove the constraint's bounds from the engine
        for (&var, &val) in &self.guard_bounds[constraint.0].lbs {
            self.lbs[var.0].remove(&val);
        }
        for (&var, &val) in &self.guard_bounds[constraint.0].ubs {
            self.ubs[var.0].remove(&val);
        }
    }

    fn is_basic(&self, var: VarId) -> bool {
        self.tableau.contains_key(&var)
    }

    fn update(&mut self, var: VarId, new_value: InfRational) {
        assert!(!self.is_basic(var), "Cannot directly update a basic variable");
        assert!(&new_value >= self.lb(var) && &new_value <= self.ub(var), "New value must be within bounds");

        for &watch in &self.t_watches[var.0] {
            let delta = self.tableau[&watch].vars[&var] * (new_value - self.val(var));
            self.assignments[watch.0] += delta;
            self.notify(watch);
        }

        self.assignments[var.0] = new_value;
        self.notify(var);
    }

    /// Runs the Simplex algorithm to restore feasibility.
    ///
    /// Repeatedly selects a basic variable whose assignment is outside its
    /// bounds and pivots it with a suitable non-basic variable until all
    /// basic variables are feasible, or a conflict is detected.
    ///
    /// Returns `Ok(())` when all variables are within their bounds, or
    /// [`PropagationError::Conflict`] with the offending constraint ids.
    pub fn check(&mut self) -> Result<(), PropagationError> {
        loop {
            // we search for a basic variable whose value is not within its bounds..
            let var = self.tableau.iter().find_map(|(&var, _)| {
                if self.val(var) < self.lb(var) {
                    Some((var, *self.lb(var)))
                } else if self.val(var) > self.ub(var) {
                    Some((var, *self.ub(var)))
                } else {
                    None
                }
            });
            if let Some((leaving, val)) = var {
                // .. if we find one, we try to pivot it with a non-basic variable that can take it back within bounds
                if self.val(leaving) < &val {
                    let entering = self.tableau[&leaving].vars.iter().find_map(|(&v, &coeff)| if coeff.is_positive() && self.val(v) < self.ub(v) || coeff.is_negative() && self.val(v) > self.lb(v) { Some(v) } else { None });
                    if let Some(entering) = entering {
                        self.pivot_and_update(entering, leaving, val);
                    } else {
                        let mut conflict = Vec::new();
                        for (vr, vl) in &self.tableau[&leaving].vars {
                            if vl.is_positive() {
                                for guard in self.ubs[vr.0].iter().next().unwrap().1.iter() {
                                    conflict.push(*guard);
                                }
                            } else if vl.is_negative() {
                                for guard in self.lbs[vr.0].iter().next_back().unwrap().1.iter() {
                                    conflict.push(*guard);
                                }
                            }
                        }
                        for guard in self.lbs[leaving.0].iter().next_back().unwrap().1.iter() {
                            conflict.push(*guard);
                        }
                        return Err(PropagationError::Conflict(conflict));
                    }
                }
                if self.val(leaving) > &val {
                    let entering = self.tableau[&leaving].vars.iter().find_map(|(&v, &coeff)| if coeff.is_positive() && self.val(v) > self.lb(v) || coeff.is_negative() && self.val(v) < self.ub(v) { Some(v) } else { None });
                    if let Some(entering) = entering {
                        self.pivot_and_update(entering, leaving, val);
                    } else {
                        let mut conflict = Vec::new();
                        for (vr, vl) in &self.tableau[&leaving].vars {
                            if vl.is_positive() {
                                for guard in self.lbs[vr.0].iter().next_back().unwrap().1.iter() {
                                    conflict.push(*guard);
                                }
                            } else if vl.is_negative() {
                                for guard in self.ubs[vr.0].iter().next().unwrap().1.iter() {
                                    conflict.push(*guard);
                                }
                            }
                        }
                        for guard in self.ubs[leaving.0].iter().next().unwrap().1.iter() {
                            conflict.push(*guard);
                        }
                        return Err(PropagationError::Conflict(conflict));
                    }
                }
            } else {
                return Ok(()); // all basic variables are within bounds, we are done
            }
        }
    }

    fn pivot_and_update(&mut self, entering: VarId, leaving: VarId, new_value: InfRational) {
        assert!(self.is_basic(leaving), "Leaving variable must be basic");
        assert!(!self.is_basic(entering), "Entering variable must be non-basic");

        let theta = (new_value - self.val(leaving)) / &self.tableau[&leaving].vars[&entering];
        self.assignments[leaving.0] = new_value;
        self.notify(leaving);
        self.assignments[entering.0] += theta;
        self.notify(entering);

        for &watch in &self.t_watches[entering.0] {
            if watch != leaving
                && let Some(row) = self.tableau.get_mut(&watch)
            {
                self.assignments[watch.0] += row.vars[&entering] * theta;
                self.notify(watch);
            }
        }

        self.pivot(entering, leaving);
    }

    fn pivot(&mut self, entering: VarId, leaving: VarId) {
        assert!(self.is_basic(leaving), "Leaving variable must be basic");
        assert!(!self.is_basic(entering), "Entering variable must be non-basic");

        // Remove the leaving variable from the watches of all variables in its tableau row
        for &var in self.tableau[&leaving].vars.keys() {
            self.t_watches[var.0].remove(&leaving);
        }

        // Rewrite the leaving variable's row to express it in terms of the entering variable
        let mut new_row = self.tableau.remove(&leaving).expect("Leaving variable must have a tableau row");
        let coeff = new_row.vars.remove(&entering).expect("Entering variable must be in the leaving variable's row");
        new_row /= &-coeff;
        new_row.vars.insert(leaving, coeff.reciprocal());

        // Substitute the new row into all other rows that contain the entering variable
        let watches = mem::take(&mut self.t_watches[entering.0]);
        for watch in &watches {
            if watch != &leaving
                && let Some(row) = self.tableau.get_mut(watch)
            {
                let (added, removed) = row.substitute(entering, &new_row);
                for v in added {
                    self.t_watches[v.0].insert(*watch);
                }
                for v in removed {
                    self.t_watches[v.0].remove(watch);
                }
            }
        }

        // Add the new row to the tableau
        self.new_row(entering, new_row);
    }

    fn new_row(&mut self, var: VarId, lin: Lin) {
        assert!(!self.is_basic(var), "Variable must be non-basic to add a new row");
        for v in lin.vars.keys() {
            self.t_watches[v.0].insert(var);
        }
        self.tableau.insert(var, lin);
    }

    fn notify(&self, var: VarId) {
        if let Some(listeners) = self.listeners.get(&var) {
            for callback in listeners {
                callback(var, self.val(var), self.lb(var), self.ub(var));
            }
        }
    }

    /// Registers a callback that is invoked whenever the value or bounds of
    /// `var` change.
    ///
    /// The callback receives `(var, new_value, new_lb, new_ub)`.
    pub fn set_listener<F>(&mut self, var: VarId, callback: F)
    where
        F: Fn(VarId, &InfRational, &InfRational, &InfRational) + 'static,
    {
        self.listeners.entry(var).or_default().push(Box::new(callback));
    }
}

impl fmt::Display for Engine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for i in 0..self.assignments.len() {
            writeln!(f, "{} = {}, [{}, {}]", VarId(i), self.val(VarId(i)), self.lb(VarId(i)), self.ub(VarId(i)))?;
        }
        for (var, lin) in &self.tableau {
            writeln!(f, "{} = {}", var, lin)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::lin::{v, vc};

    use super::*;

    #[test]
    fn engine_creation_and_variables() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();
        assert_eq!(x, VarId(0));
        assert_eq!(y, VarId(1));
        assert_eq!(e.val(x), &InfRational::ZERO);
        assert_eq!(e.lb(x), &InfRational::NEGATIVE_INFINITY);
        assert_eq!(e.ub(x), &InfRational::POSITIVE_INFINITY);
    }

    #[test]
    fn constant_le_satisfied() {
        let mut e = Engine::new();
        assert!(e.new_le(&Lin::from(5), &Lin::from(10), None).is_ok()); // 5 <= 10
        assert!(e.check().is_ok());
    }

    #[test]
    fn constant_le_unsat() {
        let mut e = Engine::new();
        assert!(e.new_le(&Lin::from(10), &Lin::from(5), None).is_err()); // 10 <= 5
    }

    #[test]
    fn constant_lt_strict_vs_nonstrict() {
        let mut e = Engine::new();
        assert!(e.new_lt(&Lin::from(0), &Lin::from(0), false, None).is_ok()); // 0 <= 0 → true
        assert!(e.new_lt(&Lin::from(0), &Lin::from(0), true, None).is_err()); // 0 < 0 → false
        assert!(e.new_lt(&Lin::from(-1), &Lin::from(0), true, None).is_ok()); // -1 < 0 → true
    }

    #[test]
    fn constant_gt_ge() {
        let mut e = Engine::new();
        assert!(e.new_ge(&Lin::from(10), &Lin::from(5), None).is_ok()); // 10 >= 5
        assert!(e.new_gt(&Lin::from(10), &Lin::from(5), false, None).is_ok()); // 10 >= 5 (non-strict)
        assert!(e.new_gt(&Lin::from(10), &Lin::from(5), true, None).is_ok()); // 10 > 5
        assert!(e.new_gt(&Lin::from(5), &Lin::from(10), true, None).is_err()); // 5 > 10 → false
    }

    #[test]
    fn constant_eq() {
        let mut e = Engine::new();
        assert!(e.new_eq(&Lin::from(7), &Lin::from(7), None).is_ok());
        assert!(e.new_eq(&Lin::from(7), &Lin::from(8), None).is_err());
    }

    #[test]
    fn single_var_le_sets_ub() {
        let mut e = Engine::new();
        let x = e.add_var();
        assert!(e.new_le(&v(x), &Lin::from(10), None).is_ok()); // x <= 10
        assert!(e.ub(x) <= &InfRational::from(Rational::from(10))); // or exact depending on inf()
        assert!(e.check().is_ok());
    }

    #[test]
    fn single_var_gt_sets_lb() {
        let mut e = Engine::new();
        let x = e.add_var();
        assert!(e.new_gt(&v(x), &Lin::from(5), true, None).is_ok()); // x > 5
        assert!(e.lb(x) >= &InfRational::from(Rational::from(5))); // adjusted for strict
        assert!(e.check().is_ok());
    }

    #[test]
    fn single_var_eq_sets_exact() {
        let mut e = Engine::new();
        let x = e.add_var();
        assert!(e.new_eq(&v(x), &Lin::from(42), None).is_ok());
        assert_eq!(e.lb(x), e.ub(x));
        assert_eq!(e.val(x), &InfRational::from(Rational::from(42)));
    }

    #[test]
    fn bound_conflict() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        let c1 = e.add_guard();
        assert!(e.new_le(&v(x), &Lin::from(10), Some(c0)).is_ok());
        assert!(e.new_gt(&v(x), &Lin::from(15), true, Some(c1)).is_ok());
        assert!(e.assert(c0).is_ok());
        let Err(PropagationError::Conflict(conflict)) = e.assert(c1) else { panic!("expected conflict") };
        assert!(conflict.contains(&c0));
        assert!(conflict.contains(&c1));
    }

    #[test]
    fn two_var_le_creates_slack() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();
        // x + y <= 5
        let lhs = vc(x, 1) + vc(y, 1);
        assert!(e.new_le(&lhs, &Lin::from(5), None).is_ok());
        assert!(e.check().is_ok());
        assert!(e.ub(VarId(e.assignments.len() - 1)) <= &InfRational::from(Rational::from(5))); // slack ub
    }

    #[test]
    fn substitution_basic_var() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();
        assert!(e.new_eq(&v(x), &(v(y) + Lin::from(3)), None).is_ok()); // x = y + 3  (adjust)
        assert!(e.new_lt(&v(y), &Lin::from(0), false, None).is_ok()); // y <= 0
        assert!(e.check().is_ok());
        // x should now be <= 3
    }

    #[test]
    fn check_pivots_to_feasibility() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();
        // Make y basic: y = 10 - x
        assert!(e.new_eq(&v(y), &(Lin::from(10) - v(x)), None).is_ok());
        // Violate y >= 12
        assert!(e.new_ge(&v(y), &Lin::from(12), None).is_ok());
        assert!(e.check().is_ok());
    }

    #[test]
    fn unsat_after_failed_pivot() {
        let mut e = Engine::new();
        let x = e.add_var();
        assert!(e.new_le(&v(x), &Lin::from(0), None).is_ok());
        let Err(PropagationError::Conflict(conflict)) = e.new_gt(&v(x), &Lin::from(10), false, None) else { panic!("expected conflict") };
        assert!(conflict.is_empty()); // no named constraints
    }

    #[test]
    fn strict_adjustment() {
        let mut e = Engine::new();
        let x = e.add_var();
        assert!(e.new_lt(&v(x), &Lin::from(0), true, None).is_ok());
        assert!(e.check().is_ok());
    }

    #[test]
    fn listener_called_on_update() {
        use std::sync::{Arc, Mutex};

        let mut engine = Engine::new();
        let a = engine.add_var();

        let called = Arc::new(Mutex::new(false));
        let called_clone = Arc::clone(&called);

        engine.set_listener(a, move |var, val, _lb, _ub| {
            assert_eq!(var, a);
            assert_eq!(val, &InfRational::from(Rational::from(5)));
            *called_clone.lock().unwrap() = true;
        });

        assert!(engine.new_eq(&v(a), &Lin::from(5), None).is_ok());
        assert!(engine.check().is_ok());
        assert!(*called.lock().unwrap());
    }

    #[test]
    fn overlap_test() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();
        assert!(e.overlap(x, y)); // both [-inf, +inf]

        assert!(e.new_le(&v(x), &Lin::from(10), None).is_ok());
        assert!(e.new_ge(&v(y), &Lin::from(20), None).is_ok());
        assert!(!e.overlap(x, y)); // [?,10] and [20,?] no overlap
    }

    #[test]
    fn display_works() {
        let mut e = Engine::new();
        let _ = e.add_var();
        let s = format!("{}", e);
        assert!(!s.is_empty());
    }

    #[test]
    fn redundant_constraint() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        let c1 = e.add_guard();
        assert!(e.new_le(&v(x), &Lin::from(10), Some(c0)).is_ok());
        assert!(e.new_le(&v(x), &Lin::from(20), Some(c1)).is_ok()); // looser → redundant
        assert!(e.check().is_ok());
    }

    #[test]
    fn shared_guard_retraction() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        assert!(e.new_le(&v(x), &Lin::from(20), Some(c0)).is_ok());
        assert!(e.new_le(&v(x), &Lin::from(10), Some(c0)).is_ok());
        assert!(e.check().is_ok());
        e.retract(c0);
        assert_eq!(e.ub(x), &InfRational::POSITIVE_INFINITY);
        assert_eq!(e.lb(x), &InfRational::NEGATIVE_INFINITY);
    }

    #[test]
    fn chained_retraction() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();
        let z = e.add_var();

        let c0 = e.add_guard();
        let c1 = e.add_guard();

        // y >= x + 1
        assert!(e.new_ge(&v(y), &(v(x) + Lin::from(1)), Some(c0)).is_ok());
        // z >= y + 1
        assert!(e.new_ge(&v(z), &(v(y) + Lin::from(1)), Some(c1)).is_ok());
        assert!(e.check().is_ok());
        e.retract(c0);
        // After retracting c0, y and z should no longer have the bounds that depended on c0
        assert_eq!(e.lb(y), &InfRational::NEGATIVE_INFINITY);
        assert_eq!(e.lb(z), &InfRational::NEGATIVE_INFINITY);

        // x >= z + 1
        assert!(e.new_ge(&v(x), &(v(z) + Lin::from(1)), None).is_ok());
        assert!(e.check().is_ok());
    }

    #[test]
    fn conflict_explanation_generation() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();

        let c0 = e.add_guard();
        let c1 = e.add_guard();
        let c2 = e.add_guard();

        // x + y >= 1
        assert!(e.new_ge(&(v(x) + v(y)), &Lin::from(1), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        // x >= 2
        assert!(e.new_ge(&v(x), &Lin::from(2), Some(c1)).is_ok());
        assert!(e.assert(c1).is_ok());
        assert!(e.check().is_ok());

        // x + y <= 0
        assert!(e.new_le(&(v(x) + v(y)), &Lin::from(0), Some(c2)).is_ok());
        assert!(e.assert(c2).is_ok());
        let Err(PropagationError::Conflict(conflict)) = e.check() else { panic!("expected conflict") };
        assert!(conflict.contains(&c0));
        assert!(conflict.contains(&c2));
    }

    #[test]
    fn complex_conflict_explanation_generation() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();
        let s1 = e.add_lin_var(vc(x, -1) + vc(y, 1)); // s1 = y - x
        let s2 = e.add_lin_var(vc(x, 1) + vc(y, 1)); // s2 = x + y

        let c0 = e.add_guard();
        assert!(e.new_le(&v(x), &Lin::from(-4), Some(c0)).is_ok()); // x <= -4
        assert!(e.assert(c0).is_ok());
        assert!(e.check().is_ok());
        let c1 = e.add_guard();
        assert!(e.new_ge(&v(x), &Lin::from(-8), Some(c1)).is_ok()); // x >= -8
        assert!(e.assert(c1).is_ok());
        assert!(e.check().is_ok());
        let c2 = e.add_guard();
        assert!(e.new_le(&v(s1), &Lin::from(1), Some(c2)).is_ok()); // s1 <= 1
        assert!(e.assert(c2).is_ok());
        assert!(e.check().is_ok());
        let c3 = e.add_guard();
        assert!(e.new_ge(&v(s2), &Lin::from(-3), Some(c3)).is_ok()); // s2 >= -3
        assert!(e.assert(c3).is_ok());
        let Err(PropagationError::Conflict(conflict)) = e.check() else { panic!("expected conflict") };
        assert!(conflict.contains(&c0));
        assert!(conflict.contains(&c2));
        assert!(conflict.contains(&c3));
    }

    #[test]
    fn add_retract_readd() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        // Add constraint: x >= 5
        assert!(e.new_ge(&v(x), &Lin::from(5), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert!(e.check().is_ok());
        assert!(e.lb(x) == &InfRational::from(Rational::from(5)));
        assert!(e.ub(x) == &InfRational::POSITIVE_INFINITY);
        assert!(e.val(x) >= &InfRational::from(Rational::from(5)));

        // Retract constraint
        e.retract(c0);
        assert!(e.check().is_ok());
        assert!(e.lb(x) == &InfRational::NEGATIVE_INFINITY);
        assert!(e.ub(x) == &InfRational::POSITIVE_INFINITY);

        // Re-add the same constraint
        assert!(e.assert(c0).is_ok());
        assert!(e.check().is_ok());
        assert!(e.lb(x) == &InfRational::from(Rational::from(5)));
        assert!(e.ub(x) == &InfRational::POSITIVE_INFINITY);
        assert!(e.val(x) >= &InfRational::from(Rational::from(5)));
    }

    #[test]
    fn tightening_bound() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        let c1 = e.add_guard();
        assert!(e.new_le(&v(x), &Lin::from(20), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert!(e.new_le(&v(x), &Lin::from(10), Some(c1)).is_ok()); // tighter
        assert!(e.assert(c1).is_ok());
        assert!(e.ub(x) <= &InfRational::from(Rational::from(10)));
    }

    #[test]
    fn test_default_trait() {
        let e = Engine::default();
        assert_eq!(e.assignments.len(), 0);
        assert_eq!(e.guard_bounds.len(), 0);
    }

    #[test]
    fn test_lin_lb_with_negative_coefficients() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();

        // Set bounds: x in [2, 5], y in [3, 7]
        assert!(e.new_ge(&v(x), &Lin::from(2), None).is_ok());
        assert!(e.new_le(&v(x), &Lin::from(5), None).is_ok());
        assert!(e.new_ge(&v(y), &Lin::from(3), None).is_ok());
        assert!(e.new_le(&v(y), &Lin::from(7), None).is_ok());

        // Test lin_lb with negative coefficient: 10 - 2*x + 3*y
        // lb = 10 - 2*ub(x) + 3*lb(y) = 10 - 2*5 + 3*3 = 10 - 10 + 9 = 9
        let lin = Lin::from(10) + vc(x, -2) + vc(y, 3);
        let lb = e.lin_lb(&lin);
        assert_eq!(lb, InfRational::from(Rational::from(9)));

        // Test lin_ub with negative coefficient
        // ub = 10 - 2*lb(x) + 3*ub(y) = 10 - 2*2 + 3*7 = 10 - 4 + 21 = 27
        let ub = e.lin_ub(&lin);
        assert_eq!(ub, InfRational::from(Rational::from(27)));
    }

    #[test]
    fn test_set_lb_tightening() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        let c1 = e.add_guard();

        // Set initial lower bound
        assert!(e.new_ge(&v(x), &Lin::from(5), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(5)));

        // Set tighter lower bound with same constraint
        assert!(e.set_lb(x, InfRational::from(Rational::from(7)), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(7)));

        // Try looser bound (should not tighten)
        assert!(e.set_lb(x, InfRational::from(Rational::from(6)), Some(c1)).is_ok());
        assert!(e.assert(c1).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(7))); // Still 7
    }

    #[test]
    fn test_set_lb_looser_does_not_leave_stale_bound_after_retract() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();

        assert!(e.new_ge(&v(x), &Lin::from(5), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(5)));

        assert!(e.set_lb(x, InfRational::from(Rational::from(7)), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(7)));

        assert!(e.set_lb(x, InfRational::from(Rational::from(6)), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(7)));

        e.retract(c0);
        assert_eq!(e.lb(x), &InfRational::NEGATIVE_INFINITY);
    }

    #[test]
    fn test_set_ub_tightening() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        let c1 = e.add_guard();

        // Set initial upper bound
        assert!(e.new_le(&v(x), &Lin::from(10), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(10)));

        // Set tighter upper bound with same constraint
        assert!(e.set_ub(x, InfRational::from(Rational::from(8)), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(8)));

        // Try looser bound (should not tighten)
        assert!(e.set_ub(x, InfRational::from(Rational::from(9)), Some(c1)).is_ok());
        assert!(e.assert(c1).is_ok());
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(8))); // Still 8
    }

    #[test]
    fn test_set_ub_looser_does_not_leave_stale_bound_after_retract() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();

        assert!(e.new_le(&v(x), &Lin::from(10), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(10)));

        assert!(e.set_ub(x, InfRational::from(Rational::from(8)), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(8)));

        assert!(e.set_ub(x, InfRational::from(Rational::from(9)), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(8)));

        e.retract(c0);
        assert_eq!(e.ub(x), &InfRational::POSITIVE_INFINITY);
    }

    #[test]
    fn test_conflict_with_basic_variable() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();

        // Make y basic: y = x + 5
        assert!(e.new_eq(&v(y), &(v(x) + Lin::from(5)), None).is_ok());

        let c0 = e.add_guard();
        let c1 = e.add_guard();

        // Constrain x: x <= 0
        assert!(e.new_le(&v(x), &Lin::from(0), Some(c0)).is_ok());
        assert!(e.assert(c0).is_ok());

        // Constrain y to conflict: y >= 10
        // This means x + 5 >= 10, so x >= 5, which conflicts with x <= 0
        assert!(e.new_ge(&v(y), &Lin::from(10), Some(c1)).is_ok());
        assert!(e.assert(c1).is_ok());
        assert!(e.check().is_err());
    }

    #[test]
    fn test_assert_method() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();

        // Manually set bounds on constraint
        e.guard_bounds[c0.0].lbs.insert(x, InfRational::from(Rational::from(5)));
        e.guard_bounds[c0.0].ubs.insert(x, InfRational::from(Rational::from(10)));

        // Assert the constraint
        assert!(e.assert(c0).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(5)));
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(10)));
    }

    #[test]
    fn test_assert_conflicting_constraint() {
        let mut e = Engine::new();
        let x = e.add_var();
        let c0 = e.add_guard();
        let c1 = e.add_guard();

        // Set initial bounds
        e.guard_bounds[c0.0].lbs.insert(x, InfRational::from(Rational::from(10)));
        assert!(e.assert(c0).is_ok());

        // Create conflicting constraint
        e.guard_bounds[c1.0].ubs.insert(x, InfRational::from(Rational::from(5)));
        assert!(e.assert(c1).is_err()); // Should fail

        // Verify the constraint was retracted
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(10)));
        // Upper bound should still be infinity (constraint was retracted)
        assert_eq!(e.ub(x), &InfRational::POSITIVE_INFINITY);
    }

    #[test]
    fn test_pivot_upper_bound_violation() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();

        // Make y basic: y = 10 - x (so when x increases, y decreases)
        assert!(e.new_eq(&v(y), &(Lin::from(10) - v(x)), None).is_ok());

        // Set bounds that will require pivoting
        assert!(e.new_le(&v(y), &Lin::from(5), None).is_ok()); // y <= 5, so 10 - x <= 5, x >= 5
        assert!(e.check().is_ok());

        // y should be at most 5
        assert!(e.val(y) <= &InfRational::from(Rational::from(5)));
    }

    #[test]
    fn test_multiple_lin_vars() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();

        // Create linear variables
        let sum = e.add_lin_var(v(x) + v(y));
        let diff = e.add_lin_var(v(x) - v(y));

        // Set constraints on linear variables
        assert!(e.new_le(&v(sum), &Lin::from(10), None).is_ok());
        assert!(e.new_ge(&v(diff), &Lin::from(2), None).is_ok());
        assert!(e.check().is_ok());
    }

    #[test]
    fn test_new_eq_with_zero_vars() {
        let mut e = Engine::new();

        // Equation with no variables (just constants)
        assert!(e.new_eq(&Lin::from(5), &Lin::from(5), None).is_ok()); // 5 == 5
        assert!(e.new_eq(&Lin::from(5), &Lin::from(3), None).is_err()); // 5 == 3
    }

    #[test]
    fn test_new_eq_with_one_var() {
        let mut e = Engine::new();
        let x = e.add_var();

        // Single variable equation: x = 5
        assert!(e.new_eq(&v(x), &Lin::from(5), None).is_ok());
        assert_eq!(e.val(x), &InfRational::from(Rational::from(5)));
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(5)));
        assert_eq!(e.ub(x), &InfRational::from(Rational::from(5)));
    }

    #[test]
    fn test_new_eq_with_multiple_vars() {
        let mut e = Engine::new();
        let x = e.add_var();
        let y = e.add_var();

        // Multiple variable equation: x + y = 10
        assert!(e.new_eq(&(v(x) + v(y)), &Lin::from(10), None).is_ok());

        // A slack variable should have been created
        assert!(e.assignments.len() > 2);
    }

    #[test]
    fn test_new_ge() {
        let mut e = Engine::new();
        let x = e.add_var();

        // x >= 5
        assert!(e.new_ge(&v(x), &Lin::from(5), None).is_ok());
        assert_eq!(e.lb(x), &InfRational::from(Rational::from(5)));
    }

    #[test]
    fn test_new_gt() {
        let mut e = Engine::new();
        let x = e.add_var();

        // x > 5 (strict)
        assert!(e.new_gt(&v(x), &Lin::from(5), true, None).is_ok());
        // Lower bound should be adjusted for strict inequality
        assert!(e.lb(x) > &InfRational::from(Rational::from(5)));
    }

    #[test]
    fn test_get_conflict_when_no_conflict() {
        let mut e = Engine::new();
        let x = e.add_var();
        assert!(e.new_le(&v(x), &Lin::from(10), None).is_ok());
        assert!(e.check().is_ok());
    }

    #[test]
    fn main() {
        let mut engine = Engine::new();
        let x = engine.add_var();
        let y = engine.add_var();

        let g1 = engine.add_guard();
        let g2 = engine.add_guard();

        // Assert constraints in order: g1 first, then g2
        engine.new_ge(&v(x), &Lin::from(5), Some(g1)).ok(); // x >= 5
        engine.assert(g1).ok(); // [1st]

        engine.new_le(&v(y), &Lin::from(10), Some(g2)).ok(); // y <= 10
        engine.assert(g2).ok(); // [2nd]

        // Key point: retract the FIRST constraint (g1), leaving g2 active
        // In a chronological (stack-like) system this would be impossible!
        // You'd have to retract g2 first, then g1. Not here.
        engine.retract(g1); // Retract the FIRST asserted constraint, even though g2 came after!

        // g1's constraint is gone, but g2's remains
        assert_eq!(engine.lb(x), &InfRational::NEGATIVE_INFINITY); // x is unbounded
        assert_eq!(engine.ub(y), &InfRational::from(Rational::from(10))); // y <= 10 still active!
    }
}
