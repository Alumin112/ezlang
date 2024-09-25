use std::collections::HashMap;
use std::num::IntErrorKind;

use crate::error::{Error, ErrorKind};
use crate::parser::syntax::{ParseResult, ParseTree, SyntaxKind};
use crate::tree::{Leaf, LeafId, Node, NodeId, TreeElement};

use super::value::{
    AssignLHS, LeafData, LeafKind, MaybeTyped, NodeData, NodeKind, Value, ValueData, ValueType,
    BUILT_INS,
};
use super::{AnalysisResult, Analyzed, AnalyzedTreeBuilder};
use SyntaxKind::*;

/// Builds the basic analyzed tree structure and
/// defines types and definitions for type checking later.
/// Detects errors such as `ByteOverflow`, `InvalidLHS` and `KeywordMisuse`.
#[derive(Debug)]
pub struct Analyzer<'a> {
    /// The source code
    source: &'a str,
    /// List of errors produced
    errors: Vec<Error<'a>>,
    /// Contains all variables mapped to memory, arranged in nexting level of scopes
    /// Vec<usize> contains all the values defined to this variable, usize is the current value
    lookup: Vec<HashMap<&'a str, (Vec<usize>, usize)>>,
    /// Current scope which is getting analyzed
    current_scope: usize,
    /// Data
    memory: Vec<Value>,
    tree: Option<ParseTree>,
    /// Tree Builder
    builder: AnalyzedTreeBuilder,
}

impl<'a> Analyzer<'a> {
    pub fn new(source: &'a str, result: ParseResult<'a>) -> Self {
        Analyzer {
            source,
            errors: result.errors,
            lookup: vec![HashMap::new()],
            current_scope: 0,
            memory: Vec::new(),
            tree: Some(result.parse),
            builder: AnalyzedTreeBuilder::new(),
        }
    }

    #[inline]
    fn get(&self, ident: &'a str) -> Option<&Value> {
        self.get_loc(ident).map(|i| &self.memory[i])
    }

    #[inline]
    fn get_loc(&self, ident: &'a str) -> Option<usize> {
        self.lookup[..=self.current_scope]
            .iter()
            .rev()
            .find_map(|map| map.get(ident).and_then(|(v, _)| v.last()))
            .copied()
    }

    #[inline]
    fn insert(&mut self, ident: &'a str, value: Value) {
        self.lookup[self.current_scope]
            .entry(ident)
            .or_insert((Vec::new(), 0))
            .0
            .push(self.memory.len());
        self.memory.push(value);
    }

    fn resolve_types(&mut self) {
        for i in 0..self.lookup.len() {
            self.current_scope = i;
            for (locs, _) in self.lookup[i].clone().values() {
                for (i, &loc) in locs.iter().enumerate() {
                    self.resolve_type(loc, i);
                }
            }
        }
    }

    fn resolve_type(&mut self, loc: usize, i: usize) {
        match &self.memory[loc].type_ {
            MaybeTyped::UnTyped(_) => {
                let MaybeTyped::UnTyped(id) =
                    std::mem::replace(&mut self.memory[loc].type_, MaybeTyped::InProgress)
                else {
                    unreachable!()
                };
                self.memory[loc].type_ = MaybeTyped::Typed(self.compute_type(id, i));
            }
            MaybeTyped::InProgress => panic!("Loopoz"),
            MaybeTyped::Typed(_) => (),
        }
    }

    fn compute_type(&mut self, id: TreeElement<NodeId, LeafId>, i: usize) -> ValueType {
        let ast = id.get_from_builder(&self.builder);
        match ast.kind() {
            Identifier => {
                let ident = &self.source[ast.span()];
                match {
                    self.lookup[..=self.current_scope]
                        .iter()
                        .rev()
                        .find_map(|map| map.get(ident).and_then(|(v, _)| v.last()))
                } {
                    Some(&t) => {
                        self.resolve_type(t, i);
                        self.lookup[..=self.current_scope]
                            .iter()
                            .rev()
                            .find_map(|map| map.get(ident).and_then(|(v, _)| v.get(i)))
                            .map(|&i| &self.memory[i])
                            .unwrap()
                            .type_
                            .type_()
                            .unwrap()
                            .clone()
                    }
                    None => ValueType::Poisoned,
                }
            }
            Value => {
                let &a = ast.into_node().unwrap().children().first().unwrap();
                self.compute_type(TreeElement::Node(a), i)
            }
            Pointer => {
                let &a = ast.into_node().unwrap().children().first().unwrap();
                ValueType::Pointer(Box::new(self.compute_type(TreeElement::Node(a), i)))
            }
            UnaryOp => {
                let mut iter = ast
                    .into_node()
                    .unwrap()
                    .children_with_leaves_builder(&self.builder);
                let op = iter.next().unwrap();
                let a = iter.next().unwrap();
                let op = self.builder.leaf(op.into_leaf().unwrap()).kind();
                let a = self.compute_type(a, i);
                a.operate_unary(op).unwrap_or(ValueType::Poisoned)
            }
            BinaryOp => {
                let mut iter = ast
                    .into_node()
                    .unwrap()
                    .children_with_leaves_builder(&self.builder);
                let a = iter.next().unwrap();
                let op = iter.next().unwrap();
                let b = iter.next().unwrap();
                let a = self.compute_type(a, i);
                let op = self.builder.leaf(op.into_leaf().unwrap()).kind();
                let b = self.compute_type(b, i);
                a.operate_binary(op, &b).unwrap_or(ValueType::Poisoned)
            }
            _ => unreachable!(),
        }
    }

    pub fn analyze(mut self) -> AnalysisResult<'a> {
        let tree = &self.tree.take().unwrap();
        let root = tree.node(ParseTree::ROOT);
        self.builder.start_node(root.kind(), root.span().start);
        for &child in root.children() {
            self.analyze_node(tree, tree.node(child));
        }
        self.builder.finish_node(root.span().end, |_| None);
        self.resolve_types();

        AnalysisResult {
            errors: self.errors,
            analyzed: Analyzed {
                tree: self.builder.finish(),
                memory: self.memory,
                lookup: self.lookup,
            },
        }
    }

    fn analyze_element(
        &mut self,
        tree: &ParseTree,
        element: TreeElement<NodeId, LeafId>,
    ) -> TreeElement<NodeId, LeafId> {
        match element {
            TreeElement::Node(id) => TreeElement::Node(self.analyze_node(tree, tree.node(id))),
            TreeElement::Leaf(id) => TreeElement::Leaf(self.analyze_leaf(tree, tree.leaf(id))),
        }
    }

    fn analyze_node(&mut self, tree: &ParseTree, node: &Node<()>) -> NodeId {
        match node.kind() {
            Statement => {
                self.builder.start_node(node.kind(), node.span().start);
                for &child in node.children() {
                    self.analyze_node(tree, tree.node(child));
                }
                self.builder.finish_node(node.span().end, |_| None)
            }
            Scope => {
                self.builder.start_node(node.kind(), node.span().start);
                self.lookup.push(HashMap::new());
                self.current_scope += 1;
                for &child in node.children() {
                    self.analyze_node(tree, tree.node(child));
                }
                self.current_scope -= 1;
                self.builder.finish_node(node.span().end, |_| None)
            }
            BinaryOp => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                let a = self
                    .analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap();
                let op = self
                    .analyze_element(tree, iter.next().unwrap())
                    .into_leaf()
                    .unwrap();
                let op = self.builder.leaf(op).kind();
                let b = self
                    .analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap();
                let a = self.builder.node(a);
                let b = self.builder.node(b);
                let type_a = a.data().as_ref().unwrap().type_();
                let type_b = b.data().as_ref().unwrap().type_();
                let type_ = if let (Some(a), Some(b)) = (type_a.type_(), type_b.type_()) {
                    Some(MaybeTyped::Typed(
                        a.operate_binary(op, b).unwrap_or(ValueType::Poisoned),
                    ))
                } else {
                    None
                };
                self.builder.finish_node(node.span().end, |id| {
                    Some(NodeData::new(NodeKind::Value(Value {
                        value: None,
                        syntax: TreeElement::Node(id),
                        type_: type_
                            .unwrap_or_else(|| MaybeTyped::UnTyped(TreeElement::Node(node.id()))),
                    })))
                })
            }
            UnaryOp => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                let a = iter.next().unwrap();
                let b = iter.next().unwrap();
                let (op, e_a) = match (a, b) {
                    (a @ TreeElement::Node(_), op @ TreeElement::Leaf(_))
                    | (op @ TreeElement::Leaf(_), a @ TreeElement::Node(_)) => (
                        self.analyze_element(tree, op)
                            .get_from_builder(&self.builder)
                            .kind(),
                        self.analyze_element(tree, a),
                    ),
                    _ => unreachable!(),
                };

                let a = e_a.get_from_builder(&self.builder).into_node().unwrap();

                let type_a = a.data().as_ref().unwrap().type_();
                let type_ = type_a
                    .type_()
                    .map(|a| MaybeTyped::Typed(a.operate_unary(op).unwrap_or(ValueType::Poisoned)));

                self.builder.finish_node(node.span().end, |id| {
                    Some(
                        NodeData::new(NodeKind::Value(Value {
                            value: None,
                            syntax: TreeElement::Node(id),
                            type_: type_.unwrap_or_else(|| {
                                MaybeTyped::UnTyped(TreeElement::Node(node.id()))
                            }),
                        }))
                        .assignable(if op == SyntaxKind::Mul {
                            AssignLHS::Deref(e_a)
                        } else {
                            AssignLHS::Invalid
                        }),
                    )
                })
            }
            Cast => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                let type_ = self
                    .analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap()
                    .get_from_builder(&self.builder)
                    .data()
                    .as_ref()
                    .unwrap()
                    .type_()
                    .clone();
                self.analyze_element(tree, iter.next().unwrap());
                self.builder.finish_node(node.span().end, |id| {
                    Some(NodeData::new(NodeKind::Value(Value {
                        value: None,
                        syntax: TreeElement::Node(id),
                        type_,
                    })))
                })
            }
            Let => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                let ident = iter.next().unwrap().into_leaf().unwrap().get(tree);
                let id = self.builder.push(ident.kind(), ident.span(), |_| None);
                let ident = &self.source[ident.span()];
                let type_ = self
                    .analyze_element(tree, iter.next().unwrap())
                    .get_from_builder(&self.builder)
                    .type_()
                    .clone();
                self.insert(
                    ident,
                    Value {
                        value: None,
                        syntax: TreeElement::Leaf(id),
                        type_,
                    },
                );
                self.builder.finish_node(node.span().end, |_| None)
            }
            ReLet => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                let lhs = self
                    .analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap();
                self.analyze_element(tree, iter.next().unwrap());
                self.analyze_element(tree, iter.next().unwrap());
                let lhs = lhs.get_from_builder(&self.builder);
                let data_lhs = lhs.data().as_ref().unwrap();
                if data_lhs.assignable == AssignLHS::Invalid {
                    self.errors
                        .push(Error::error(ErrorKind::InvalidLHS, lhs.span(), self.source));
                }
                self.builder.finish_node(node.span().end, |_| None)
            }
            Pointer => {
                self.builder.start_node(node.kind(), node.span().start);
                let type_ = self
                    .analyze_element(tree, node.children_with_leaves(tree).next().unwrap())
                    .get_from_builder(&self.builder)
                    .type_()
                    .clone()
                    .map(|v| ValueType::Pointer(Box::new(v)));
                self.builder.finish_node(node.span().end, |id| {
                    Some(NodeData::new(NodeKind::Value(Value {
                        value: None,
                        syntax: TreeElement::Node(id),
                        type_,
                    })))
                })
            }
            Loop => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut elements = node.children_with_leaves(tree).collect::<Vec<_>>();
                let body = elements.pop().unwrap();
                let mut iter = elements.split(|s| {
                    s.into_leaf()
                        .map(|s| s.get(tree).kind() == SemiColon)
                        .unwrap_or(false)
                });
                if let Some(&[e]) = iter.next() {
                    self.analyze_element(tree, e);
                } else {
                    self.builder.push(Stuffing, 0..0, |id| {
                        Some(LeafData::new(LeafKind::Value(Value {
                            value: None,
                            syntax: TreeElement::Leaf(id),
                            type_: MaybeTyped::Typed(ValueType::None),
                        })))
                    });
                }

                if let Some(&[e]) = iter.next() {
                    self.analyze_element(tree, e);
                } else {
                    self.builder.push(Stuffing, 0..0, |id| {
                        Some(LeafData::new(LeafKind::Value(Value {
                            value: None,
                            syntax: TreeElement::Leaf(id),
                            type_: MaybeTyped::Typed(ValueType::Number),
                        })))
                    });
                }

                if let Some(&[e]) = iter.next() {
                    self.analyze_element(tree, e);
                } else {
                    self.builder.push(Stuffing, 0..0, |id| {
                        Some(LeafData::new(LeafKind::Value(Value {
                            value: None,
                            syntax: TreeElement::Leaf(id),
                            type_: MaybeTyped::Typed(ValueType::None),
                        })))
                    });
                }
                self.analyze_element(tree, body);
                self.builder.finish_node(node.span().end, |_| None)
            }
            If => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                self.analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap();
                self.analyze_element(tree, iter.next().unwrap());
                iter.next().map(|e| self.analyze_element(tree, e));
                self.builder.finish_node(node.span().end, |_| None)
            }
            Ternary => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                self.analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap();
                let then = self
                    .analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap();
                self.analyze_element(tree, iter.next().unwrap())
                    .into_node()
                    .unwrap();

                let type_then = then
                    .get_from_builder(&self.builder)
                    .data()
                    .as_ref()
                    .unwrap()
                    .type_()
                    .clone();
                self.builder.finish_node(node.span().end, |id| {
                    Some(NodeData::new(NodeKind::Value(Value {
                        value: None,
                        syntax: TreeElement::Node(id),
                        type_: type_then,
                    })))
                })
            }
            Call => {
                self.builder.start_node(node.kind(), node.span().start);
                let mut iter = node.children_with_leaves(tree);
                let f = self.analyze_element(tree, iter.next().unwrap());
                iter.for_each(|v| {
                    self.analyze_element(tree, v);
                });
                let type_ = if let MaybeTyped::Typed(ValueType::FnPtr(v)) =
                    f.get_from_builder(&self.builder).type_()
                {
                    MaybeTyped::Typed(v.last().cloned().unwrap())
                } else {
                    MaybeTyped::UnTyped(TreeElement::Node(node.id()))
                };
                self.builder.finish_node(node.span().end, |id| {
                    Some(NodeData::new(NodeKind::Value(Value {
                        value: None,
                        syntax: TreeElement::Node(id),
                        type_,
                    })))
                })
            }
            Fx => {
                self.builder.start_node(node.kind(), node.span().start);
                self.lookup.push(HashMap::new());
                self.current_scope += 1;
                let mut iter = node.children_with_leaves(tree);
                let name = iter.next().unwrap().into_leaf().unwrap().get(tree);
                self.builder.push(name.kind(), name.span(), |_| None);
                let mut args = iter.collect::<Vec<_>>();
                let body = args.pop().unwrap();
                for arg in args {
                    let arg = arg.into_leaf().unwrap().get(tree);
                    let id = self.builder.push(arg.kind(), arg.span(), |_| None);
                    self.insert(
                        &self.source[arg.span()],
                        Value {
                            value: None,
                            syntax: TreeElement::Leaf(id),
                            // type_: MaybeTyped::UnTyped(TreeElement::Leaf(id)),
                            type_: MaybeTyped::Typed(ValueType::Number),
                        },
                    );
                }
                self.analyze_element(tree, body);
                self.current_scope -= 1;
                self.builder.finish_node(node.span().end, |_| None)
            }
            Value => {
                self.builder.start_node(node.kind(), node.span().start);
                let a = self
                    .analyze_element(tree, node.children_with_leaves(tree).next().unwrap())
                    .get_from_builder(&self.builder);

                let type_ = a.type_().clone();
                let assignable = a.assignable();

                self.builder.finish_node(node.span().end, |id| {
                    Some(
                        NodeData::new(NodeKind::Value(Value {
                            value: None,
                            syntax: TreeElement::Node(id),
                            type_,
                        }))
                        .assignable(assignable),
                    )
                })
            }
            Kind => {
                self.builder.start_node(node.kind(), node.span().start);
                let type_ = match node
                    .children_with_leaves(tree)
                    .next()
                    .unwrap()
                    .into_leaf()
                    .unwrap()
                    .get(tree)
                    .kind()
                {
                    ByteKw => MaybeTyped::Typed(ValueType::Number),
                    SemiColon => MaybeTyped::Typed(ValueType::None),
                    Identifier => todo!(),
                    _ => unreachable!(),
                };
                self.builder.finish_node(node.span().end, |id| {
                    Some(NodeData::new(NodeKind::Value(Value {
                        value: None,
                        syntax: TreeElement::Node(id),
                        type_,
                    })))
                })
            }
            Error => {
                self.builder.start_node(node.kind(), node.span().start);
                for element in node.children_with_leaves(tree) {
                    self.analyze_element(tree, element);
                }
                self.builder.finish_node(node.span().end, |id| {
                    Some(NodeData::new(NodeKind::Value(Value {
                        value: None,
                        syntax: TreeElement::Node(id),
                        type_: MaybeTyped::Typed(ValueType::Poisoned),
                    })))
                })
            }
            s => todo!("{s}"),
        }
    }

    fn analyze_leaf(&mut self, _tree: &ParseTree, leaf: &Leaf<SyntaxKind>) -> LeafId {
        match leaf.kind() {
            Add | Mul | Div | Sub | Mod | And | Or | Not | Shl | Shr | Equal | NotEqual | Xor
            | LessThan | LessEqual | GreaterThan | GreaterEqual | Assign => {
                self.builder.push(leaf.kind(), leaf.span(), |_| None)
            }
            AddAssign | SubAssign | MulAssign | DivAssign | ModAssign | AndAssign | OrAssign
            | XorAssign | ShlAssign | ShrAssign => {
                self.builder.push(leaf.kind(), leaf.span(), |_| None)
            }
            Number => self.builder.push(leaf.kind(), leaf.span(), |id| {
                Some(LeafData::new(LeafKind::Value(Value {
                    value: Some(ValueData::Number(self.source[leaf.span()].parse().unwrap())),
                    syntax: TreeElement::Leaf(id),
                    type_: MaybeTyped::Typed(ValueType::Number),
                })))
            }),
            SemiColon => self.builder.push(leaf.kind(), leaf.span(), |id| {
                Some(LeafData::new(LeafKind::Value(Value {
                    value: Some(ValueData::None),
                    syntax: TreeElement::Leaf(id),
                    type_: MaybeTyped::Typed(ValueType::None),
                })))
            }),
            InKw => self.builder.push(leaf.kind(), leaf.span(), |id| {
                Some(LeafData::new(LeafKind::Value(Value {
                    value: None,
                    syntax: TreeElement::Leaf(id),
                    type_: MaybeTyped::Typed(ValueType::Number),
                })))
            }),
            Error => self.builder.push(leaf.kind(), leaf.span(), |id| {
                Some(LeafData::new(LeafKind::Value(Value {
                    value: None,
                    syntax: TreeElement::Leaf(id),
                    type_: MaybeTyped::Typed(ValueType::Poisoned),
                })))
            }),
            Char => {
                let s = &self.source[leaf.span()];
                let mut chars = s[1..s.len() - 1].chars();
                let c = match chars.next().unwrap() {
                    '\\' => match chars.next().unwrap() {
                        'n' => b'\n',
                        't' => b'\t',
                        'r' => b'\r',
                        c @ ('\\' | '\'' | '\"') => c as u8,
                        'x' => u8::from_str_radix(&s[3..s.len() - 1], 16).unwrap_or_else(|err| {
                            match err.kind() {
                                IntErrorKind::PosOverflow => {
                                    self.errors.push(Error::error(
                                        ErrorKind::ByteOverflow,
                                        leaf.span(),
                                        self.source,
                                    ));
                                    0
                                }
                                _ => unreachable!(),
                            }
                        }),
                        '0'..='7' => u8::from_str_radix(&s[2..s.len() - 1], 8).unwrap_or_else(
                            |err| match err.kind() {
                                IntErrorKind::PosOverflow => {
                                    self.errors.push(Error::error(
                                        ErrorKind::ByteOverflow,
                                        leaf.span(),
                                        self.source,
                                    ));
                                    0
                                }
                                _ => unreachable!(),
                            },
                        ),
                        _ => unreachable!(),
                    },
                    c => c as u8,
                };
                self.builder.push(leaf.kind(), leaf.span(), |id| {
                    Some(LeafData::new(LeafKind::Value(Value {
                        value: Some(ValueData::Char(c)),
                        syntax: TreeElement::Leaf(id),
                        type_: MaybeTyped::Typed(ValueType::Number),
                    })))
                })
            }
            String => {
                let mut new = Vec::new();
                let s = &self.source[leaf.span()];
                let mut chars = s[1..s.len() - 1].chars().enumerate().peekable();
                while let Some((i, c)) = chars.next() {
                    new.push(match c {
                        '\\' => match chars.next().unwrap().1 {
                            'n' => b'\n',
                            't' => b'\t',
                            'r' => b'\r',
                            c @ ('\\' | '\'' | '\"') => c as u8,
                            'x' => {
                                let i = i + 3;
                                let mut j = i;
                                while matches!(chars.peek(), Some((_, c)) if c.is_ascii_hexdigit())
                                {
                                    j += 1;
                                    chars.next();
                                }
                                u8::from_str_radix(&s[i..j], 16).unwrap_or_else(|err| {
                                    match err.kind() {
                                        IntErrorKind::PosOverflow => {
                                            self.errors.push(Error::error(
                                                ErrorKind::ByteOverflow,
                                                leaf.span(),
                                                self.source,
                                            ));
                                            0
                                        }
                                        e => unreachable!("{e:?}"),
                                    }
                                })
                            }
                            '0'..='7' => {
                                let i = i + 2;
                                let mut j = i + 1;
                                while matches!(chars.peek(), Some((_, '0'..='7'))) {
                                    j += 1;
                                    chars.next();
                                }
                                u8::from_str_radix(&s[i..j], 8).unwrap_or_else(|err| {
                                    match err.kind() {
                                        IntErrorKind::PosOverflow => {
                                            self.errors.push(Error::error(
                                                ErrorKind::ByteOverflow,
                                                leaf.span(),
                                                self.source,
                                            ));
                                            0
                                        }
                                        _ => unreachable!(),
                                    }
                                })
                            }
                            _ => unreachable!(),
                        },
                        c => c as u8,
                    });
                }
                new.push(0);
                self.builder.push(leaf.kind(), leaf.span(), move |id| {
                    Some(LeafData::new(LeafKind::Value(Value {
                        value: Some(ValueData::String(new)),
                        syntax: TreeElement::Leaf(id),
                        type_: MaybeTyped::Typed(ValueType::Pointer(Box::new(ValueType::Number))),
                    })))
                })
            }
            Identifier => {
                let type_ = self
                    .get(&self.source[leaf.span()])
                    .and_then(|v| v.type_.type_().cloned())
                    .or_else(|| {
                        BUILT_INS
                            .get(&self.source[leaf.span()])
                            .map(|b| b.value_type())
                    })
                    .map(MaybeTyped::Typed);
                self.builder.push(leaf.kind(), leaf.span(), |id| {
                    Some(
                        LeafData::new(LeafKind::Value(Value {
                            value: None,
                            syntax: TreeElement::Leaf(id),
                            type_: type_.unwrap_or_else(|| {
                                MaybeTyped::UnTyped(TreeElement::Leaf(leaf.id()))
                            }),
                        }))
                        .assignable(AssignLHS::Ident),
                    )
                })
            }
            s => unreachable!("{s}"),
        }
    }
}
