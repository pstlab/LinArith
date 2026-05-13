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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropagationError {
    Conflict(Vec<ConstraintId>), // The constraints that caused the conflict
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

    pub fn new_constraint(&mut self) -> ConstraintId {
        let index = self.constraints.len();
        self.constraints.push(Constraint { lbs: HashMap::new(), ubs: HashMap::new() });
        ConstraintId(index)
    }

    pub fn val(&self, var: VarId) -> &InfRational {
        &self.assignments[var.0]
    }

    pub fn lb(&self, var: VarId) -> &InfRational {
        self.lbs[var.0].iter().next_back().map(|(lb, _)| lb).unwrap_or(&InfRational::NEGATIVE_INFINITY)
    }

    pub fn ub(&self, var: VarId) -> &InfRational {
        self.ubs[var.0].iter().next().map(|(ub, _)| ub).unwrap_or(&InfRational::POSITIVE_INFINITY)
    }

    pub fn lin_val(&self, lin: &Lin) -> InfRational {
        let mut result = i_rat(lin.known_term);
        for (&var, &coeff) in &lin.vars {
            result += coeff * self.val(var);
        }
        result
    }

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

    fn _is_basic(&self, var: VarId) -> bool {
        self.tableau.contains_key(&var)
    }

    fn _notify(&self, var: VarId) {
        if let Some(listeners) = self.listeners.get(&var) {
            for callback in listeners {
                callback(var, self.val(var), self.lb(var), self.ub(var));
            }
        }
    }

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
