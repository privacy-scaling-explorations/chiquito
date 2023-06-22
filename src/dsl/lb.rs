use super::cb::{Constraint, Typing};
use crate::ast::{self, Expr};
use core::fmt::Debug;

#[derive(Default, Clone)]
pub struct LookupTable<F> {
    pub annotation: String,
    pub destination_columns: Vec<Expr<F>>,
}

pub fn lookup_table<F: Debug + Clone, E: Into<Expr<F>>>(
    annotation: String,
    destination_columns: Vec<E>,
) -> LookupTable<F> {
    let destination_columns = destination_columns.into_iter().map(|e| e.into()).collect();
    LookupTable::new(annotation, destination_columns)
}

impl<F: Debug + Clone> LookupTable<F> {
    fn new(annotation: String, destination_columns: Vec<Expr<F>>) -> LookupTable<F> {
        LookupTable {
            annotation,
            destination_columns,
        }
    }

    pub fn r#match<E: Into<Constraint<F>>>(&self, source_columns: Vec<E>) -> Lookup<F> {
        let mut lookup = Lookup::<F>::default();

        let destination_columns = self.destination_columns.clone();
        destination_columns.into_iter().for_each(|destination| {
            lookup.exprs.push((None, destination));
        });

        lookup.r#match(source_columns)
    }

    pub fn enable<C: Into<Constraint<F>>>(&self, enable: C) -> Lookup<F> {
        let mut lookup = Lookup::<F>::default();

        let destination_columns = self.destination_columns.clone();
        destination_columns.into_iter().for_each(|destination| {
            lookup.exprs.push((None, destination));
        });

        lookup.enable(enable)
    }
}

#[derive(Clone)]
pub struct Lookup<F> {
    pub annotation: String,
    pub exprs: Vec<(Option<Constraint<F>>, Expr<F>)>,
    pub enable: Option<Constraint<F>>,
}

impl<F> Default for Lookup<F> {
    fn default() -> Self {
        Lookup {
            annotation: String::new(),
            exprs: Vec::<(Option<Constraint<F>>, Expr<F>)>::new(),
            enable: None,
        }
    }
}

impl<F: Debug + Clone> Lookup<F> {
    pub fn r#match<E: Into<Constraint<F>>>(mut self, source_columns: Vec<E>) -> Self {
        self.exprs.iter().for_each(|(source, _)| {
            if source.is_some() {
                panic!("Can not call match on a lookup table that's already matched.");
            }
        });

        let source_columns: Vec<Constraint<F>> =
            source_columns.into_iter().map(|e| e.into()).collect();
        if source_columns.len() != self.exprs.len() {
            panic!(
                "Expected {} source columns, got {}",
                self.exprs.len(),
                source_columns.len()
            );
        }

        match self.enable.clone() {
            None => {
                for (index, source_column) in source_columns.into_iter().enumerate() {
                    self.exprs[index].0 = Some(source_column);
                    self.annotation += &format!(
                        "match({} => {:?}) ",
                        &self.exprs[index].0.as_ref().unwrap().annotation,
                        &self.exprs[index].1
                    );
                }
            }
            Some(enable) => {
                for (index, source_column) in source_columns.into_iter().enumerate() {
                    self.exprs[index].0 =
                        Some(Self::multiply_constraints(enable.clone(), source_column));
                    self.annotation += &format!(
                        "match({} => {:?}) ",
                        &self.exprs[index].0.as_ref().unwrap().annotation,
                        &self.exprs[index].1
                    );
                }
            }
        }

        self
    }

    pub fn enable<C: Into<Constraint<F>>>(mut self, enable: C) -> Self {
        let enable = enable.into();

        match self.enable {
            None => {
                if enable.typing == Typing::AntiBooly {
                    panic!(
                        "Expected Boolean or Unknown for enable, got AntiBooly (enable: {})",
                        enable.annotation
                    )
                }
                // Multiply all LHS constraints by the enabler
                for (source, _) in &mut self.exprs {
                    *source = Some(Self::multiply_constraints(
                        enable.clone(),
                        source.clone().unwrap(),
                    ));
                }
                self.annotation = format!("if {}, ", &enable.annotation) + &self.annotation;
                self.enable = Some(enable);
            }
            Some(_) => panic!("Can not call enable on a lookup table that's already enabled."),
        }

        self
    }

    fn multiply_constraints(enable: Constraint<F>, constraint: Constraint<F>) -> Constraint<F> {
        Constraint {
            annotation: constraint.annotation.clone(), /* annotation only takes the constraint's
                                                        * annotation, because enabler's
                                                        * annotation is already included in the
                                                        * enable function above in the format of
                                                        * "if {enable}" */
            expr: enable.expr * constraint.expr,
            typing: constraint.typing, // Typing of the source column.
        }
    }

    pub(crate) fn convert_to_ast_lookup(self) -> ast::Lookup<F> {
        let exprs = self
            .exprs
            .iter()
            .map(|(source, destination)| {
                if source.is_none() {
                    panic!("Can not add a lookup that misses source column.")
                }
                let source = ast::Constraint {
                    annotation: source.clone().unwrap().annotation,
                    expr: source.clone().unwrap().expr,
                };
                (source, destination.clone())
            })
            .collect();

        let enable = if let Some(enable) = self.enable {
            Some(ast::Constraint {
                annotation: enable.annotation.clone(),
                expr: enable.expr,
            })
        } else {
            None
        };

        ast::Lookup {
            annotation: self.annotation,
            exprs,
            enable,
        }
    }
}
