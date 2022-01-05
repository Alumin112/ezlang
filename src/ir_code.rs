use std::collections::HashMap;

use super::utils::{Error, ErrorType, Instruction, Instructions, Node, TokenType, Val, ValType};

/// Generates the Intermediate 3-address code from the AST
pub struct CodeGenerator {
    instructions: Instructions,
    array_index: usize,
    vars: HashMap<String, Val>,
}

impl CodeGenerator {
    fn match_node(&mut self, node: &Node) -> Result<(Val, bool), Error> {
        match node {
            Node::Number(num) => match num.token_type {
                TokenType::Number(num1) => Ok((Val::Num(num1 as i32), false)),
                TokenType::Keyword(ref boolean) => match boolean.as_ref() {
                    "true" => Ok((Val::Bool(true), false)),
                    "false" => Ok((Val::Bool(false), false)),
                    _ => unreachable!(),
                },
                _ => unreachable!(),
            },

            Node::BinaryOp(op, left, right) => {
                let (left, _) = self.match_node(left)?;
                let (right, _) = self.match_node(right)?;
                let left_type = left.r#type();
                if left_type != right.r#type() {
                    return Err(Error::new(
                        ErrorType::TypeError,
                        op.position,
                        format!(
                            "Cannot do {} for {:?} and {:?}",
                            op,
                            right.r#type(),
                            left_type
                        ),
                    ));
                }
                self.instructions.push(
                    Instruction::from_token_binary(op)(left, right),
                    Some(self.array_index),
                );
                self.array_index += 1;
                Ok((Val::Index(self.array_index - 1, left_type), false))
            }

            Node::UnaryOp(op, expr) => {
                let (expr, _) = self.match_node(expr)?;
                let expr_type = expr.r#type();
                self.instructions.push(
                    Instruction::from_token_unary(op)(expr),
                    Some(self.array_index),
                );
                self.array_index += 1;
                Ok((Val::Index(self.array_index - 1, expr_type), false))
            }

            Node::VarAssign(var, expr) => {
                if let TokenType::Identifier(ref var) = var.token_type {
                    match self.match_node(expr)? {
                        (Val::Index(index, type_), _) => {
                            self.vars
                                .insert(var.clone(), Val::Index(self.array_index, type_));
                            self.instructions.push(
                                Instruction::Copy(Val::Index(index, type_)),
                                Some(self.array_index),
                            );
                            self.array_index += 1;
                            Ok((Val::Index(self.array_index - 1, type_), false))
                        }
                        (val, _) => {
                            let val_type = val.r#type();
                            self.vars.insert(var.clone(), val);
                            Ok((Val::Index(self.array_index, val_type), false))
                        }
                    }
                } else {
                    unreachable!();
                }
            }

            Node::VarAccess(var) => {
                if let TokenType::Identifier(ref var) = var.token_type {
                    Ok((self.vars.get(var).cloned().unwrap(), false))
                } else {
                    unreachable!();
                }
            }

            Node::VarReassign(var1, expr) => {
                if let TokenType::Identifier(ref var) = var1.token_type {
                    match self.match_node(expr)? {
                        (Val::Index(index, type_), _) => {
                            let var = self.vars.get_mut(var).unwrap();
                            if var.r#type() != type_ {
                                return Err(Error::new(
                                    ErrorType::TypeError,
                                    var1.position,
                                    format!(
                                        "Variable {} is of type {:?} but is being assigned {:?}",
                                        var1,
                                        var.r#type(),
                                        type_
                                    ),
                                ));
                            }
                            *var = Val::Index(index, var.r#type());
                            self.instructions.push(
                                Instruction::Copy(Val::Index(index, type_)),
                                Some(self.array_index),
                            );
                            self.array_index += 1;
                            Ok((Val::Index(self.array_index, type_), false))
                        }
                        (val, _) => {
                            let var = self.vars.get_mut(var).unwrap();
                            let val_type = val.r#type();
                            if var.r#type() != val_type {
                                return Err(Error::new(
                                    ErrorType::TypeError,
                                    var1.position,
                                    format!(
                                        "Variable {} is of type {:?} but is being assigned {:?}",
                                        var1,
                                        var.r#type(),
                                        val_type
                                    ),
                                ));
                            }
                            *var = val;
                            Ok((Val::Index(self.array_index, val_type), false))
                        }
                    }
                } else {
                    unreachable!();
                }
            }

            Node::Statements(statements) => {
                for statement in statements {
                    let (val, return_) = self.match_node(statement)?;
                    if return_ {
                        return Ok((val, false));
                    }
                }
                Ok((Val::None, false))
            }

            Node::Print(expr) => {
                let (expr, _) = self.match_node(expr)?;
                self.instructions.push(Instruction::Print(expr), None);
                Ok((Val::Index(self.array_index, ValType::None), false))
            }

            Node::Ascii(expr) => {
                let (expr, _) = self.match_node(expr)?;
                self.instructions.push(Instruction::Ascii(expr), None);
                Ok((Val::Index(self.array_index, ValType::None), false))
            }

            Node::Input => {
                self.instructions
                    .push(Instruction::Input, Some(self.array_index));
                self.array_index += 1;
                Ok((Val::Index(self.array_index - 1, ValType::Number), false))
            }

            Node::If(cond1, then1, else_1) => {
                let (cond, _) = self.match_node(cond1)?;
                if cond.r#type() != ValType::Boolean {
                    return Err(Error::new(
                        ErrorType::TypeError,
                        cond1.position(),
                        format!(
                            "Condition in an if statement can only be a boolean, and not a {:?}",
                            cond.r#type()
                        ),
                    ));
                }
                let (then, _) = self.match_node(then1)?;
                let then_type = then.r#type();
                let else_ = match else_1.as_ref().map(|e| self.match_node(e)) {
                    Some(Ok((else_, _))) => {
                        if then_type != else_.r#type() {
                            return Err(Error::new(
                                ErrorType::TypeError,
                                else_1.as_ref().unwrap().position(),
                                format!("Then and else branch have different types, expected type {:?}, found type {:?}", then_type, else_.r#type()),
                            ));
                        }
                        Some(else_)
                    }
                    Some(Err(e)) => {
                        return Err(e);
                    }
                    None => None,
                };
                self.instructions
                    .push(Instruction::If(cond, then, else_), Some(self.array_index));
                self.array_index += 1;
                Ok((Val::Index(self.array_index - 1, then_type), false))
            }

            Node::None => Ok((Val::None, false)),

            Node::Call(_, _) => todo!(),
            Node::FuncDef(_, _, _) => todo!(),

            Node::Return(_, expr) => match expr {
                Some(expr) => Ok((self.match_node(expr)?.0, true)),
                None => Ok((Val::None, true)),
            },
        }
    }
}

/// Generates and returns the Intermediate Representation of the AST
pub fn generate_code(ast: Node) -> Result<Instructions, Error> {
    let mut obj = CodeGenerator {
        instructions: Instructions::new(),
        array_index: 0,
        vars: HashMap::new(),
    };
    obj.match_node(&ast)?;
    Ok(obj.instructions)
}
