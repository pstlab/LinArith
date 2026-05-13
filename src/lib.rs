mod constraint;
mod inf_rational;
mod lin;
mod rational;
mod var;

use crate::constraint::ConstraintId;
pub use inf_rational::{InfRational, i_i, i_rat, inf, inf_i};
pub use lin::{Lin, c, v, vc};
pub use rational::{Rational, r, rat};
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt,
};
pub use var::VarId;

type Callback = Box<dyn Fn(VarId, &InfRational, &InfRational, &InfRational)>; // Callback type for variable changes: (variable index, new value, new lower bound, new upper bound)

struct Constraint {
    lbs: HashMap<VarId, InfRational>, // variables' lower bounds set by this constraint
    ubs: HashMap<VarId, InfRational>, // variables' upper bounds set by this constraint
}

pub struct Engine {
    assignments: Vec<InfRational>,                          // the current variable assignments
    lbs: Vec<BTreeMap<InfRational, HashSet<ConstraintId>>>, // lower bounds for each variable, mapping from bound to the set of constraints that set it
    ubs: Vec<BTreeMap<InfRational, HashSet<ConstraintId>>>, // upper bounds for each variable, mapping from bound to the set of constraints that set it
    constraints: Vec<Constraint>,                           // list of constraints, each containing the bounds it sets on variables
    tableau: BTreeMap<VarId, Lin>,                          // the tableau, mapping basic variable indices to their corresponding linear expressions
    t_watches: Vec<HashSet<VarId>>,                         // for each variable, the set of tableau rows that watch it (i.e., contain it in their expression)
    listeners: HashMap<VarId, Vec<Callback>>,               // listeners for variable changes, indexed by variable index
}

/// An error returned when constraint propagation detects an inconsistency.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropagationError {
    /// The solver found a contradiction. The contained list identifies the
    /// [`ConstraintId`]s whose bounds jointly caused the conflict.
    Conflict(Vec<ConstraintId>),
}

impl Engine {
    pub fn new() -> Self {
        Engine {
            assignments: Vec::new(),
            lbs: Vec::new(),
            ubs: Vec::new(),
            constraints: Vec::new(),
            tableau: BTreeMap::new(),
            t_watches: Vec::new(),
            listeners: HashMap::new(),
        }
    }

    pub fn add_var(&mut self) -> VarId {
        let index = self.assignments.len();
        self.assignments.push(InfRational::ZERO);
        self.lbs.push(BTreeMap::new());
        self.ubs.push(BTreeMap::new());
        self.t_watches.push(HashSet::new());
        VarId(index)
    }

    /// Allocates a new constraint slot and returns its [`ConstraintId`].
    ///
    /// After creation, bounds can be associated with the constraint via
    /// [`set_lb`](Self::set_lb) / [`set_ub`](Self::set_ub) using this id as
    /// the `reason`, and the constraint can then be activated with
    /// [`assert`](Self::assert).
    pub fn new_constraint(&mut self) -> ConstraintId {
        let index = self.constraints.len();
        self.constraints.push(Constraint { lbs: HashMap::new(), ubs: HashMap::new() });
        ConstraintId(index)
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
        let mut result = i_rat(lin.known_term);
        for (&var, &coeff) in &lin.vars {
            result += coeff * self.val(var);
        }
        result
    }

    /// Computes the tightest lower bound of a linear expression given the
    /// current variable bounds.
    pub fn lin_lb(&self, lin: &Lin) -> InfRational {
        let mut result = i_rat(lin.known_term);
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
        let mut result = i_rat(lin.known_term);
        for (&var, &coeff) in &lin.vars {
            if coeff.is_positive() {
                result += coeff * self.ub(var);
            } else {
                result += coeff * self.lb(var);
            }
        }
        result
    }

    /// Asserts that `var >= lb`, attributed to the optional `reason` constraint.
    ///
    /// If the new lower bound exceeds the current upper bound, a
    /// [`PropagationError::Conflict`] is returned immediately without modifying
    /// state. Otherwise the bound is recorded and, if the non-basic variable's
    /// current value falls below `lb`, its assignment is updated accordingly.
    ///
    /// # Panics
    /// Panics if `lb` is negative infinity.
    pub fn set_lb(&mut self, var: VarId, lb: InfRational, reason: Option<ConstraintId>) -> Result<(), PropagationError> {
        assert!(lb > InfRational::NEGATIVE_INFINITY, "Lower bound cannot be negative infinity");
        let mut conflict = Vec::new();
        if &lb > self.ub(var) {
            if let Some(reason) = reason {
                conflict.push(reason);
            }
            for reason in self.ubs[var.0].iter().next().unwrap().1.iter() {
                conflict.push(*reason);
            }
            return Err(PropagationError::Conflict(conflict)); // Inconsistent constraint
        }

        if let Some(reason) = reason {
            if let Some(c_lb) = self.constraints[reason.0].lbs.get(&var) {
                if c_lb < &lb {
                    self.lbs[var.0].remove(c_lb);
                    self.lbs[var.0].entry(lb).or_default().insert(reason);
                    self.constraints[reason.0].lbs.insert(var, lb);
                }
            } else {
                self.constraints[reason.0].lbs.insert(var, lb);
            }
        }

        let entry = self.lbs[var.0].entry(lb).or_default();
        if let Some(reason) = reason {
            entry.insert(reason);
        }
        if self.val(var) < &lb && !self.is_basic(var) {
            self.update(var, lb);
        }

        Ok(())
    }

    /// Asserts that `var <= ub`, attributed to the optional `reason` constraint.
    ///
    /// If the new upper bound falls below the current lower bound, a
    /// [`PropagationError::Conflict`] is returned immediately without modifying
    /// state. Otherwise the bound is recorded and, if the non-basic variable's
    /// current value exceeds `ub`, its assignment is updated accordingly.
    ///
    /// # Panics
    /// Panics if `ub` is positive infinity.
    pub fn set_ub(&mut self, var: VarId, ub: InfRational, reason: Option<ConstraintId>) -> Result<(), PropagationError> {
        assert!(ub < InfRational::POSITIVE_INFINITY, "Upper bound cannot be positive infinity");
        let mut conflict = Vec::new();
        if &ub < self.lb(var) {
            if let Some(reason) = reason {
                conflict.push(reason);
            }
            for reason in self.lbs[var.0].iter().next_back().unwrap().1.iter() {
                conflict.push(*reason);
            }
            return Err(PropagationError::Conflict(conflict)); // Inconsistent constraint
        }

        if let Some(reason) = reason {
            if let Some(c_ub) = self.constraints[reason.0].ubs.get(&var) {
                if c_ub > &ub {
                    self.ubs[var.0].remove(c_ub);
                    self.ubs[var.0].entry(ub).or_default().insert(reason);
                    self.constraints[reason.0].ubs.insert(var, ub);
                }
            } else {
                self.constraints[reason.0].ubs.insert(var, ub);
            }
        }

        let entry = self.ubs[var.0].entry(ub).or_default();
        if let Some(reason) = reason {
            entry.insert(reason);
        }
        if self.val(var) > &ub && !self.is_basic(var) {
            self.update(var, ub);
        }

        Ok(())
    }

    /// Activates all bounds registered under `constraint`.
    ///
    /// Each lower/upper bound stored in the constraint is applied via
    /// [`set_lb`](Self::set_lb) / [`set_ub`](Self::set_ub). On the first
    /// conflict the constraint is automatically retracted and the error is
    /// returned.
    pub fn assert(&mut self, constraint: ConstraintId) -> Result<(), PropagationError> {
        // Add the constraint's bounds to the engine
        for (var, val) in std::mem::take(&mut self.constraints[constraint.0].lbs) {
            if let Err(e) = self.set_lb(var, val, Some(constraint)) {
                self.retract(constraint);
                return Err(e);
            }
        }
        for (var, val) in std::mem::take(&mut self.constraints[constraint.0].ubs) {
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
    pub fn retract(&mut self, constraint: ConstraintId) {
        // Remove the constraint's bounds from the engine
        for (&var, &val) in &self.constraints[constraint.0].lbs {
            self.lbs[var.0].remove(&val);
        }
        for (&var, &val) in &self.constraints[constraint.0].ubs {
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
                                for reason in self.ubs[vr.0].iter().next().unwrap().1.iter() {
                                    conflict.push(*reason);
                                }
                            } else if vl.is_negative() {
                                for reason in self.lbs[vr.0].iter().next_back().unwrap().1.iter() {
                                    conflict.push(*reason);
                                }
                            }
                        }
                        for reason in self.lbs[leaving.0].iter().next_back().unwrap().1.iter() {
                            conflict.push(*reason);
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
                                for reason in self.lbs[vr.0].iter().next_back().unwrap().1.iter() {
                                    conflict.push(*reason);
                                }
                            } else if vl.is_negative() {
                                for reason in self.ubs[vr.0].iter().next().unwrap().1.iter() {
                                    conflict.push(*reason);
                                }
                            }
                        }
                        for reason in self.ubs[leaving.0].iter().next().unwrap().1.iter() {
                            conflict.push(*reason);
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
        let watches = std::mem::take(&mut self.t_watches[entering.0]);
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
