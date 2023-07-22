use std::{
    collections::HashMap,
    fmt::Debug,
    sync::{Arc, Mutex},
};

use crate::{
    ast::{Expr, Lookup},
    util::{uuid, UUID},
};

use super::{cb::Constraint, StepTypeSetupContext};

pub trait LookupBuilder<F> {
    fn build(self, ctx: &StepTypeSetupContext<F>) -> Lookup<F>;
}

/// A helper struct for building lookup tables.
pub struct InPlaceLookupBuilder<F> {
    lookup: Lookup<F>,
}

impl<F> LookupBuilder<F> for InPlaceLookupBuilder<F> {
    fn build(self, _: &StepTypeSetupContext<F>) -> Lookup<F> {
        self.lookup
    }
}

impl<F> Default for InPlaceLookupBuilder<F> {
    fn default() -> Self {
        InPlaceLookupBuilder {
            lookup: Lookup::default(),
        }
    }
}

impl<F: Debug + Clone> InPlaceLookupBuilder<F> {
    /// Adds a source column-lookup column pair to the lookup table. Because the function returns a
    /// mutable reference to the `LookupBuilder<F>`, it can an chain multiple `add` and `enable`
    /// function calls to build the lookup table. Requires calling `lookup` to create an empty
    /// `LookupBuilder` instance at the very front.
    pub fn add<C: Into<Constraint<F>>, E: Into<Expr<F>>>(
        mut self,
        constraint: C,
        expression: E,
    ) -> Self {
        let constraint = constraint.into();
        self.lookup
            .add(constraint.annotation, constraint.expr, expression.into());
        self
    }

    /// Adds a selector column specific to the lookup table. Because the function returns a mutable
    /// reference to the `LookupBuilder<F>`, it can an chain multiple `add` and `enable` function
    /// calls to build the lookup table. Requires calling `lookup` to create an
    /// empty `LookupBuilder` instance at the very front.
    pub fn enable<C: Into<Constraint<F>>>(mut self, enable: C) -> Self {
        let enable = enable.into();
        self.lookup.enable(enable.annotation, enable.expr);
        self
    }
}

#[derive(Debug, Clone)]
pub struct LookupTable<F> {
    id: UUID,
    dest: Vec<Expr<F>>,
}

impl<F> Default for LookupTable<F> {
    fn default() -> Self {
        Self {
            id: uuid(),
            dest: Default::default(),
        }
    }
}

impl<F> LookupTable<F> {
    #[allow(clippy::should_implement_trait)]
    pub fn add<E: Into<Expr<F>>>(mut self, expr: E) -> Self {
        self.dest.push(expr.into());

        self
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }
}

impl<F: Debug + Clone> LookupTable<F> {
    pub fn build(self, src: Vec<Constraint<F>>, enable: Option<Constraint<F>>) -> Lookup<F> {
        assert_eq!(
            self.dest.len(),
            src.len(),
            "number of source and destination parameters doesn't match"
        );

        let mut lookup = Lookup::default();

        if let Some(enable) = enable {
            lookup.enable(enable.annotation, enable.expr);
        }

        src.into_iter()
            .zip(self.dest)
            .for_each(|(src, dest)| lookup.add(src.annotation, src.expr, dest));

        lookup
    }
}

#[derive(Debug)]
pub struct LookupTableRegistry<F>(Arc<Mutex<HashMap<UUID, LookupTable<F>>>>);

impl<F> Clone for LookupTableRegistry<F> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<F> Default for LookupTableRegistry<F> {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(HashMap::new())))
    }
}

impl<F> LookupTableRegistry<F> {
    pub fn add(&self, table: LookupTable<F>) {
        self.0.lock().as_mut().unwrap().insert(table.uuid(), table);
    }
}

impl<F: Clone> LookupTableRegistry<F> {
    pub fn get(&self, uuid: UUID) -> LookupTable<F> {
        (*self.0.lock().unwrap().get(&uuid).unwrap()).clone()
    }
}
