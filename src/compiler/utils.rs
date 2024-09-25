use std::collections::HashMap;

use crate::{
    analyzer::{
        value::{AssignLHS, LeafData, NodeData, ValueData, ValueType},
        AnalyzedTree,
    },
    parser::syntax::SyntaxKind as SK,
    tree::{Leaf, LeafId, Node, NodeId, TreeElement},
};

pub struct FunctionBuilder {
    ir: Vec<(SK, Vec<Value>)>
}

pub struct Value {
        
}
