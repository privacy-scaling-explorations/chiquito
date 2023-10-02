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
pub struct LookupTableStore<F> {
    id: UUID,
    dest: Vec<Expr<F>>,
}

impl<F> Default for LookupTableStore<F> {
    fn default() -> Self {
        Self {
            id: uuid(),
            dest: Default::default(),
        }
    }
}

impl<F> LookupTableStore<F> {
    #[allow(clippy::should_implement_trait)]
    pub fn add<E: Into<Expr<F>>>(mut self, expr: E) -> Self {
        self.dest.push(expr.into());

        self
    }

    pub fn uuid(&self) -> UUID {
        self.id
    }
}

impl<F: Debug + Clone> LookupTableStore<F> {
    fn build(self, src: Vec<Constraint<F>>, enable: Option<Constraint<F>>) -> Lookup<F> {
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
pub struct LookupTableRegistry<F>(Arc<Mutex<HashMap<UUID, LookupTableStore<F>>>>);

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
    pub fn add(&self, table: LookupTableStore<F>) {
        self.0.lock().as_mut().unwrap().insert(table.uuid(), table);
    }
}

impl<F: Clone> LookupTableRegistry<F> {
    pub fn get(&self, uuid: UUID) -> LookupTableStore<F> {
        (*self.0.lock().unwrap().get(&uuid).unwrap()).clone()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LookupTable {
    pub(crate) uuid: UUID,
}

impl LookupTable {
    pub fn apply<F, C: Into<Constraint<F>>>(&self, constraint: C) -> LookupTableBuilder<F> {
        LookupTableBuilder::new(self.uuid).apply(constraint)
    }

    /// Adds a selector column specific to the lookup table. Because the function returns a mutable
    /// reference to the `LookupBuilder<F>`, it can an chain multiple `add` and `enable` function
    /// calls to build the lookup table. Requires calling `lookup` to create an
    /// empty `LookupBuilder` instance at the very front.
    pub fn when<F, C: Into<Constraint<F>>>(&self, enable: C) -> LookupTableBuilder<F> {
        LookupTableBuilder::new(self.uuid).when(enable)
    }
}

pub struct LookupTableBuilder<F> {
    id: UUID,
    src: Vec<Constraint<F>>,
    enable: Option<Constraint<F>>,
}

impl<F> LookupTableBuilder<F> {
    fn new(id: UUID) -> Self {
        Self {
            id,
            src: Default::default(),
            enable: Default::default(),
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn apply<C: Into<Constraint<F>>>(mut self, constraint: C) -> Self {
        self.src.push(constraint.into());

        self
    }

    /// Adds a selector column specific to the lookup table. Because the function returns a mutable
    /// reference to the `LookupBuilder<F>`, it can an chain multiple `add` and `enable` function
    /// calls to build the lookup table. Requires calling `lookup` to create an
    /// empty `LookupBuilder` instance at the very front.
    pub fn when<C: Into<Constraint<F>>>(mut self, enable: C) -> Self {
        if self.enable.is_some() {
            panic!("Cannot use when operator in lookup table more than once.")
        }

        self.enable = Some(enable.into());

        self
    }
}

impl<F: Clone + Debug> LookupBuilder<F> for LookupTableBuilder<F> {
    fn build(self, ctx: &StepTypeSetupContext<F>) -> Lookup<F> {
        let table = ctx.tables.get(self.id);

        table.build(self.src, self.enable)
    }
}

#[cfg(test)]
mod test {

    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2curves::ff::Field;

    use crate::ast::StepType;
    use crate::ast::Expr;

    use super::*;

    #[test]
    fn test_in_place_lookup_builder_build() {
        let in_place_lookup_builder = InPlaceLookupBuilder::<Fr>::default();
        let annotation = in_place_lookup_builder.lookup.annotation;
        let exprs = in_place_lookup_builder.lookup.exprs;
        let enable = in_place_lookup_builder.lookup.enable;
        assert_eq!(annotation, "");
        assert_eq!(format!("{:?}",exprs), "[]");
        assert_eq!(format!("{:?}", enable), "None");
    }

    #[test]
    fn test_in_place_lookup_builder_add() {
        let mut in_place_lookup_builder = InPlaceLookupBuilder::<Fr>::default();
        let constraint = Constraint::from(Expr::Const(Fr::ONE));
        in_place_lookup_builder = in_place_lookup_builder.add(
            constraint,
            Expr::Const(Fr::ONE),
        );
        let annotation = &in_place_lookup_builder.lookup.annotation;
        let exprs = &in_place_lookup_builder.lookup.exprs;
        let enable = &in_place_lookup_builder.lookup.enable;
        assert_eq!(annotation, "match(0x1 => 0x1) ");
        assert_eq!(format!("{:?}",exprs), "[(Constraint { annotation: \"0x1\", expr: 0x1 }, 0x1)]");
        assert_eq!(format!("{:?}", enable), "None");
    }

    #[test]
    fn test_in_place_lookup_builder_enable() {
        let mut in_place_lookup_builder = InPlaceLookupBuilder::<Fr>::default();
        let constraint = Constraint::from(Expr::Const(Fr::ONE));
        in_place_lookup_builder = in_place_lookup_builder.enable(
            constraint
        );
        let annotation = &in_place_lookup_builder.lookup.annotation;
        let exprs = &in_place_lookup_builder.lookup.exprs;
        let enable = &in_place_lookup_builder.lookup.enable;
        assert_eq!(annotation, "if 0x1, ");
        assert_eq!(format!("{:?}",exprs), "[]");
        assert_eq!(format!("{:?}", enable), "Some(Constraint { annotation: \"0x1\", expr: 0x1 })");
    }

    #[test]
    fn test_lookup_table_store_add() {
        let lookup_table_store = LookupTableStore::<Fr>::default();
        let copied = lookup_table_store.add(Expr::Const(Fr::ONE)).clone();
        assert_eq!(format!("{:?}", copied.dest[0]), "0x1");
    }

    #[test]
    fn test_lookup_table_store_uuid() {
        let lookup_table_store = LookupTableStore::<Fr>::default();
        let copied = lookup_table_store.clone();
        let uuid = lookup_table_store.uuid();
        assert_eq!(uuid, copied.id);
    }

    #[test]
    fn test_lookup_table_store_build_none_enable() {
        let lookup_table_store = LookupTableStore::<Fr>::default();
        let copied = lookup_table_store.add(Expr::Const(Fr::ONE)).clone();
        let constraint = Constraint::from(Expr::Const(Fr::ONE));
        let built_lookup = copied.build(vec!(constraint), None);
        assert_eq!(built_lookup.annotation, "match(0x1 => 0x1) ");
        assert_eq!(format!("{:?}", built_lookup.exprs), "[(Constraint { annotation: \"0x1\", expr: 0x1 }, 0x1)]");
        assert_eq!(format!("{:?}", built_lookup.enable), "None");
    }

    #[test]
    fn test_lookup_table_store_build_enalbed() {
        let lookup_table_store = LookupTableStore::<Fr>::default();
        let copied = lookup_table_store.add(Expr::Const(Fr::ONE)).clone();
        let constraint = Constraint::from(Expr::Const(Fr::ONE));
        let copied_constraint = constraint.clone();
        let built_lookup = copied.build(vec!(constraint), Some(copied_constraint));
        assert_eq!(built_lookup.annotation, "if 0x1, match(0x1 => 0x1) ");
        assert_eq!(format!("{:?}", built_lookup.exprs), "[(Constraint { annotation: \"0x1\", expr: (0x1 * 0x1) }, 0x1)]");
        assert_eq!(format!("{:?}", built_lookup.enable), "Some(Constraint { annotation: \"0x1\", expr: 0x1 })");
    }

    #[test]
    fn test_lookup_table_registry_add() {
        let lookup_table_store = LookupTableStore::<Fr>::default();
        let stored_uuid = lookup_table_store.uuid();
        let lookup_table_registry = LookupTableRegistry::<Fr>::default();
        lookup_table_registry.add(lookup_table_store);
        let stored_lookup_table = lookup_table_registry.get(stored_uuid);
        assert!(format!("{:?}", stored_lookup_table).contains(&format!("LookupTableStore {{ id: {}, dest: [] }}", stored_uuid)));
    }

    #[test]
    fn test_lookup_table_registry_clone() {
        let lookup_table_store = LookupTableStore::<Fr>::default();
        let stored_uuid = lookup_table_store.uuid();
        let lookup_table_registry = LookupTableRegistry::<Fr>::default();
        lookup_table_registry.add(lookup_table_store);
        let copied_lookup_table = lookup_table_registry.clone();
        let stored_lookup_table = lookup_table_registry.get(stored_uuid);
        let stored_lookup_table_in_copy = copied_lookup_table.get(stored_uuid);
        assert_eq!(format!("{:?}", stored_lookup_table), format!("{:?}", stored_lookup_table_in_copy));
    }

    #[test]
    fn test_lookup_table_apply() {
        let constraint = Constraint::from(Expr::Const(Fr::ONE));
        let lookup_table = LookupTable { uuid: 1u128 };
        let applied_lookup_table = lookup_table.apply(constraint);
        let id = applied_lookup_table.id;
        let src = applied_lookup_table.src;
        let enable = applied_lookup_table.enable;
        assert_eq!(format!("{:?}", id), "1");
        assert_eq!(format!("{:?}", src), "[0x1]");
        assert_eq!(format!("{:?}", enable), "None");
    }

    #[test]
    fn test_lookup_table_when() {
        let enable = Constraint::from(Expr::Const(Fr::ONE));
        let lookup_table = LookupTable { uuid: 1u128 };
        let applied_lookup_table = lookup_table.when(enable);
        let id = applied_lookup_table.id;
        let src = applied_lookup_table.src;
        let enable = applied_lookup_table.enable;
        assert_eq!(format!("{:?}", id), "1");
        assert_eq!(format!("{:?}", src), "[]");
        assert_eq!(format!("{:?}", enable), "Some(0x1)");
    }

    #[test]
    fn test_lookup_table_builder_new() {
        let mut lookup_table_builder = LookupTableBuilder::<Fr>::new(1u128);
        let constraint = Constraint::from(Expr::Const(Fr::ONE));
        let constraint2 = Constraint::from(Expr::Const(Fr::ZERO));
        lookup_table_builder = lookup_table_builder.apply(constraint);
        lookup_table_builder = lookup_table_builder.apply(constraint2);
        let id = lookup_table_builder.id;
        let src = lookup_table_builder.src;
        assert_eq!(format!("{:?}", id), "1");
        assert_eq!(format!("{:?}", src), "[0x1, 0x]");
    }

    #[test]
    fn test_lookup_table_builder_when() {
        let mut lookup_table_builder = LookupTableBuilder::<Fr>::new(1u128);
        let constraint = Constraint::from(Expr::Const(Fr::ONE));
        lookup_table_builder = lookup_table_builder.when(constraint);
        let enable = lookup_table_builder.enable;
        assert_eq!(format!("{:?}", enable), "Some(0x1)");
    }

    #[test]
    fn test_lookup_table_builder_build() {
        let lookup_table_store = LookupTableStore::<Fr>::default();
        let stored_uuid = lookup_table_store.uuid();
        let lookup_table_builder = LookupTableBuilder::<Fr>::new(stored_uuid);
        let lookup_table_registry = LookupTableRegistry::<Fr>::default();
        lookup_table_registry.add(lookup_table_store);
        let mut step_type = StepType::<Fr>::new(0u128, "test step type".to_string());
        let step_type_setup_context = StepTypeSetupContext { 
            step_type: &mut step_type, 
            tables: lookup_table_registry 
        };
        let result = lookup_table_builder.build(&step_type_setup_context);
        let annotation = result.annotation.clone();
        let exprs = result.exprs.clone();
        let enable = result.enable.clone();
        assert_eq!(annotation, "");
        assert_eq!(format!("{:?}",exprs), "[]");
        assert_eq!(format!("{:?}", enable), "None");
    }

}
