use crate::utils::{Position, Type};

use super::utils::{Error, ErrorType, Node, Scope, Token, TokenType, ASSIGNMENT_OPERATORS};

/// A result type for parsing
type ParseResult = Result<Node, Error>;

/// Parses the List of Tokens into an AST
pub struct Parser {
    tokens: Vec<Token>,
    token_index: usize,
    current_token: Token,
}

impl Parser {
    fn advance(&mut self) {
        self.token_index += 1;
        if self.token_index < self.tokens.len() {
            self.current_token = self.tokens[self.token_index].clone();
        }
    }

    fn peek_type(&self) -> Option<TokenType> {
        if self.token_index + 1 < self.tokens.len() {
            return Some(self.tokens[self.token_index + 1].token_type.clone());
        }
        None
    }

    fn statements(&mut self, end_token: TokenType, global: bool, scope: &mut Scope) -> ParseResult {
        let mut statements = vec![];
        let mut pos = self.current_token.position.clone();
        if !global {
            self.advance();
        }

        while self.current_token.token_type != end_token {
            match self.current_token.token_type {
                TokenType::Eol => self.advance(),
                _ => statements.push(self.statement(scope)?),
            }
        }
        let end_pos = self.current_token.position.clone();
        self.advance();
        pos.end = end_pos.end;
        pos.line_end = end_pos.line_end;
        Ok(Node::Statements(statements, pos))
    }

    fn statement(&mut self, scope: &mut Scope) -> ParseResult {
        match self.current_token.token_type {
            TokenType::Keyword(ref keyword) => match keyword.as_ref() {
                // break, continue
                "ezreturn" => {
                    let token = self.current_token.clone();
                    self.advance();
                    if self.current_token.token_type == TokenType::Eol {
                        Ok(Node::Return(None, token.position))
                    } else {
                        Ok(Node::Return(
                            Some(Box::new(self.expression(scope)?)),
                            token.position,
                        ))
                    }
                }
                "let" => {
                    self.advance();
                    let node = self.let_statement(true, scope)?;
                    scope.register_variable(node.clone());
                    Ok(node)
                }
                "if" => {
                    let mut pos = self.current_token.position.clone();
                    self.advance();
                    let condition = self.expression(scope)?;
                    let then_branch = self.statement(scope)?;
                    let (else_, end_pos) = if self.current_token.token_type
                        == TokenType::Keyword("else".to_string())
                    {
                        self.advance();
                        let node = self.statement(scope)?;
                        let pos = node.position();
                        (Some(Box::new(node)), pos)
                    } else {
                        self.advance();
                        (None, self.current_token.position.clone())
                    };
                    pos.end = end_pos.end;
                    pos.line_end = end_pos.line_end;
                    Ok(Node::If(
                        Box::new(condition),
                        Box::new(then_branch),
                        else_,
                        pos,
                    ))
                }
                "ezascii" => {
                    let mut pos = self.current_token.position.clone();
                    self.advance();
                    let mut nodes = vec![self.expression(scope)?];
                    while let TokenType::Comma = self.current_token.token_type {
                        self.advance();
                        nodes.push(self.expression(scope)?);
                    }
                    pos.end = self.current_token.position.end;
                    pos.line_end = self.current_token.position.line_end;
                    Ok(Node::Ascii(nodes, pos))
                }
                "ezout" => {
                    let mut pos = self.current_token.position.clone();
                    self.advance();
                    let mut nodes = vec![self.expression(scope)?];
                    while let TokenType::Comma = self.current_token.token_type {
                        self.advance();
                        nodes.push(self.expression(scope)?);
                    }
                    pos.end = self.current_token.position.end;
                    pos.line_end = self.current_token.position.line_end;
                    Ok(Node::Print(nodes, pos))
                }
                _ => self.expression(scope),
            },
            TokenType::Identifier(_)
                if self.peek_type().is_some()
                    && ASSIGNMENT_OPERATORS.contains(&self.peek_type().unwrap()) =>
            {
                let node = self.let_statement(false, scope)?;
                scope.access_variable(node.clone());
                Ok(node)
            }
            _ => self.expression(scope),
        }
    }

    fn expression(&mut self, scope: &mut Scope) -> ParseResult {
        self.binary_op(
            Self::comparison,
            vec![TokenType::LAnd, TokenType::LOr, TokenType::LXor],
            Self::comparison,
            scope,
        )
    }

    fn make_type(&mut self) -> Result<Type, Error> {
        match self.current_token.token_type {
            TokenType::Keyword(ref keyword) => match keyword.as_ref() {
                "eznumber" => {
                    self.advance();
                    Ok(Type::Number)
                }
                "ezbool" => {
                    self.advance();
                    Ok(Type::Boolean)
                }
                "ezblank" => {
                    self.advance();
                    Ok(Type::None)
                }
                _ => Err(Error::new(
                    ErrorType::SyntaxError,
                    self.current_token.position.clone(),
                    format!("Expected type, found {}", keyword),
                )),
            },
            TokenType::BAnd => {
                self.advance();
                Ok(Type::Ref(Box::new(self.make_type()?)))
            }
            TokenType::LAnd => {
                self.advance();
                Ok(Type::Ref(Box::new({
                    Type::Ref(Box::new(self.make_type()?))
                })))
            }
            TokenType::LParen => {
                self.advance();
                let mut types = vec![];
                if self.current_token.token_type != TokenType::RParen {
                    types.push(self.make_type()?);
                    while self.current_token.token_type == TokenType::Comma {
                        self.advance();
                        types.push(self.make_type()?);
                    }
                    if self.current_token.token_type != TokenType::RParen {
                        return Err(Error::new(
                            ErrorType::SyntaxError,
                            self.current_token.position.clone(),
                            "Expected ')'".to_string(),
                        ));
                    }
                }
                self.advance();
                let ret = if self.current_token.token_type == TokenType::Arrow {
                    self.advance();
                    self.make_type()?
                } else {
                    Type::None
                };
                Ok(Type::Function(types, Box::new(ret)))
            }
            _ => Err(Error::new(
                ErrorType::SyntaxError,
                self.current_token.position.clone(),
                format!("Expected type, found {}", self.current_token),
            )),
        }
    }

    fn let_statement(&mut self, init: bool, scope: &mut Scope) -> ParseResult {
        if let TokenType::Identifier(_) = self.current_token.token_type {
            let token = self.current_token.clone();
            self.advance();
            let t = if self.current_token.token_type == TokenType::Colon {
                self.advance();
                Some(self.make_type()?)
            } else {
                None
            };
            match self.current_token.token_type {
                TokenType::Assign if init => {
                    self.advance();
                    Ok(Node::VarAssign(token, Box::new(self.expression(scope)?), t))
                }
                TokenType::Assign => {
                    self.advance();
                    Ok(Node::VarReassign(token, Box::new(self.expression(scope)?)))
                }
                ref x if ASSIGNMENT_OPERATORS.contains(x) && !init => {
                    let op = self.current_token.clone();
                    self.advance();
                    let right = self.expression(scope)?;

                    if [TokenType::DivAssign, TokenType::ModAssign].contains(&op.token_type) {
                        if let Node::Number(Token {
                            token_type: TokenType::Number(0),
                            ..
                        }) = right
                        {
                            return Err(Error::new(
                                ErrorType::DivisionByZero,
                                self.current_token.position.clone(),
                                "Division by zero".to_string(),
                            ));
                        }
                    }

                    Ok(Node::VarReassign(
                        token.clone(),
                        Box::new(Node::BinaryOp(
                            op.un_augmented(),
                            Box::new(Node::VarAccess(token)),
                            Box::new(right),
                        )),
                    ))
                }
                _ => Err(Error::new(
                    ErrorType::SyntaxError,
                    self.current_token.position.clone(),
                    format!("Expected '=', found {}", self.current_token),
                )),
            }
        } else {
            Err(Error::new(
                ErrorType::SyntaxError,
                self.current_token.position.clone(),
                format!("Expected an identifier, found {}", self.current_token),
            ))
        }
    }

    fn comparison(&mut self, scope: &mut Scope) -> ParseResult {
        if let TokenType::LNot = self.current_token.token_type {
            let token = self.current_token.clone();
            self.advance();
            Ok(Node::UnaryOp(token, Box::new(self.comparison(scope)?)))
        } else {
            self.binary_op(
                Self::bitwise,
                vec![
                    TokenType::Eq,
                    TokenType::Neq,
                    TokenType::Lt,
                    TokenType::Gt,
                    TokenType::Le,
                    TokenType::Ge,
                ],
                Self::bitwise,
                scope,
            )
        }
    }

    fn bitwise(&mut self, scope: &mut Scope) -> ParseResult {
        self.binary_op(
            Self::arithmetic,
            vec![
                TokenType::BAnd,
                TokenType::BOr,
                TokenType::BXor,
                TokenType::Shl,
                TokenType::Shr,
            ],
            Self::arithmetic,
            scope,
        )
    }

    fn arithmetic(&mut self, scope: &mut Scope) -> ParseResult {
        self.binary_op(
            Self::term,
            vec![TokenType::Add, TokenType::Sub],
            Self::term,
            scope,
        )
    }

    fn term(&mut self, scope: &mut Scope) -> ParseResult {
        self.binary_op(
            Self::factor,
            vec![TokenType::Mul, TokenType::Div, TokenType::Mod],
            Self::factor,
            scope,
        )
    }

    fn factor(&mut self, scope: &mut Scope) -> ParseResult {
        let token = self.current_token.clone();
        match token.token_type {
            TokenType::Sub | TokenType::BNot | TokenType::Inc | TokenType::Dec => {
                self.advance();
                Ok(Node::UnaryOp(token, Box::new(self.factor(scope)?)))
            }
            _ => self.power(scope),
        }
    }

    fn power(&mut self, scope: &mut Scope) -> ParseResult {
        self.binary_op(Self::call, vec![TokenType::Pow], Self::call, scope)
    }

    fn call(&mut self, scope: &mut Scope) -> ParseResult {
        if let TokenType::Identifier(_) = self.current_token.token_type {
            let atom = Node::VarAccess(self.current_token.clone());
            let mut pos = self.current_token.position.clone();
            self.advance();
            if let TokenType::LParen = self.current_token.token_type {
                self.advance();
                let mut args = vec![];
                while self.current_token.token_type != TokenType::RParen {
                    args.push(self.expression(scope)?);
                    if self.current_token.token_type != TokenType::Comma {
                        break;
                    }
                    self.advance();
                }
                if self.current_token.token_type != TokenType::RParen {
                    return Err(Error::new(
                        ErrorType::SyntaxError,
                        self.current_token.position.clone(),
                        format!("Expected ')', found {}", self.current_token),
                    ));
                }
                self.advance();
                pos.end = self.current_token.position.end;
                pos.line_end = self.current_token.position.line_end;
                let node = Node::Call(Box::new(atom), args, pos);
                scope.access_function(node.clone());
                return Ok(node);
            } else {
                self.token_index -= 1;
            }
        }
        self.current_token = self.tokens[self.token_index].clone();
        self.atom(scope)
    }

    fn atom(&mut self, scope: &mut Scope) -> ParseResult {
        let token = self.current_token.clone();
        match token.token_type {
            TokenType::Keyword(ref keyword) => match keyword.as_ref() {
                "ez" => {
                    self.advance();
                    let node = self.function_definition(scope)?;
                    scope.register_function(node.clone());
                    Ok(node)
                }
                "ezin" => {
                    self.advance();
                    Ok(Node::Input(token.position))
                }
                "true" => {
                    self.advance();
                    Ok(Node::Number(token))
                }
                "false" => {
                    self.advance();
                    Ok(Node::Number(token))
                }
                "ezblank" => {
                    self.advance();
                    Ok(Node::None(token.position))
                }
                _ => Err(Error::new(
                    ErrorType::SyntaxError,
                    self.current_token.position.clone(),
                    format!("Unexpected keyword: {}", self.current_token),
                )),
            },
            TokenType::TernaryIf => {
                self.advance();
                let condition = self.expression(scope)?;
                let then_branch = self.expression(scope)?;
                if self.current_token.token_type != TokenType::Colon {
                    return Err(Error::new(
                        ErrorType::SyntaxError,
                        self.current_token.position.clone(),
                        format!("Expected ':', found {}", self.current_token),
                    ));
                }
                self.advance();
                let else_branch = self.expression(scope)?;
                let mut pos = token.position;
                let end_pos = else_branch.position();
                pos.end = end_pos.end;
                pos.line_end = end_pos.line_end;
                Ok(Node::Ternary(
                    Box::new(condition),
                    Box::new(then_branch),
                    Box::new(else_branch),
                    pos,
                ))
            }
            TokenType::Identifier(_) => {
                self.advance();
                let node = Node::VarAccess(token);
                scope.access_variable(node.clone());
                Ok(node)
            }
            TokenType::LParen => {
                self.advance();
                if self.current_token.token_type == TokenType::RParen {
                    self.advance();
                    return Ok(Node::Tuple(token.position));
                }
                let node = self.expression(scope)?;
                if self.current_token.token_type != TokenType::RParen {
                    return Err(Error::new(
                        ErrorType::SyntaxError,
                        self.current_token.position.clone(),
                        format!("Expected ')', found {}", self.current_token),
                    ));
                }
                self.advance();
                Ok(node)
            }
            TokenType::LCurly => {
                let mut new_scope = Scope::new(Some(scope));
                let node = self.statements(TokenType::RCurly, false, &mut new_scope)?;
                scope.scopes.push(new_scope);
                Ok(node)
            }
            TokenType::Number(_) => {
                self.advance();
                Ok(Node::Number(token))
            }
            TokenType::Mul => {
                self.advance();
                let mut pos = token.position;
                pos.end = self.current_token.position.end;
                pos.line_end = self.current_token.position.line_end;
                Ok(Node::Deref(Box::new(self.atom(scope)?), pos))
            }
            TokenType::Pow => {
                self.advance();
                let mut pos = token.position;
                pos.end = self.current_token.position.end - 1;
                pos.line_end = self.current_token.position.line_end;
                let node = Node::Deref(Box::new(self.atom(scope)?), pos.clone());
                pos.start += 1;
                Ok(Node::Deref(Box::new(node), pos))
            }
            TokenType::BAnd => {
                self.advance();
                let mut pos = token.position;
                pos.end = self.current_token.position.end;
                pos.line_end = self.current_token.position.line_end;
                Ok(Node::Ref(Box::new(self.atom(scope)?), pos))
            }
            TokenType::LAnd => {
                self.advance();
                let mut pos = token.position;
                pos.end = self.current_token.position.end - 1;
                pos.line_end = self.current_token.position.line_end;
                let node = Node::Ref(Box::new(self.atom(scope)?), pos.clone());
                pos.start += 1;
                Ok(Node::Ref(Box::new(node), pos))
            }
            _ => Err(Error::new(
                ErrorType::SyntaxError,
                self.current_token.position.clone(),
                format!("Unexpected token: {}", self.current_token),
            )),
        }
    }

    fn function_definition(&mut self, scope: &mut Scope) -> ParseResult {
        let name = if let TokenType::Identifier(_) = self.current_token.token_type {
            self.current_token.clone()
        } else {
            return Err(Error::new(
                ErrorType::SyntaxError,
                self.current_token.position.clone(),
                format!("Expected an identifier, found {}", self.current_token),
            ));
        };
        self.advance();
        if self.current_token.token_type != TokenType::LParen {
            return Err(Error::new(
                ErrorType::SyntaxError,
                self.current_token.position.clone(),
                format!("Expected '(', found {}", self.current_token),
            ));
        }
        self.advance();
        let mut params = vec![];
        if let TokenType::Identifier(_) = self.current_token.token_type {
            let p = self.current_token.clone();
            self.advance();
            if self.current_token.token_type != TokenType::Colon {
                return Err(Error::new(
                    ErrorType::SyntaxError,
                    self.current_token.position.clone(),
                    format!("Expected ':', found {}", self.current_token),
                ));
            }
            self.advance();
            let t = self.make_type()?;
            params.push((p, t));
            while self.current_token.token_type == TokenType::Comma {
                self.advance();
                if let TokenType::Identifier(_) = self.current_token.token_type {
                    let p = self.current_token.clone();
                    self.advance();
                    if self.current_token.token_type != TokenType::Colon {
                        return Err(Error::new(
                            ErrorType::SyntaxError,
                            self.current_token.position.clone(),
                            format!("Expected ':', found {}", self.current_token),
                        ));
                    }
                    self.advance();
                    let t = self.make_type()?;
                    params.push((p, t));
                } else {
                    return Err(Error::new(
                        ErrorType::SyntaxError,
                        self.current_token.position.clone(),
                        format!("Expected identifier, found {}", self.current_token),
                    ));
                }
            }
            if self.current_token.token_type != TokenType::RParen {
                return Err(Error::new(
                    ErrorType::SyntaxError,
                    self.current_token.position.clone(),
                    format!("Expected ')' or ',', found {}", self.current_token),
                ));
            }
        } else if self.current_token.token_type != TokenType::RParen {
            return Err(Error::new(
                ErrorType::SyntaxError,
                self.current_token.position.clone(),
                format!("Expected identifier or ')', found {}", self.current_token),
            ));
        }
        self.advance();

        let ret = if self.current_token.token_type == TokenType::Arrow {
            self.advance();
            self.make_type()?
        } else {
            Type::None
        };

        let mut new_scope = Scope::new(Some(scope));
        new_scope.args = Some(params.iter().map(|x| x.0.clone()).collect());
        let expr = self.expression(&mut new_scope)?;
        scope.scopes.push(new_scope);
        let mut pos = name.position.clone();
        pos.end = expr.position().end;
        pos.line_end = expr.position().line_end;
        Ok(Node::FuncDef(name, params, Box::new(expr), ret, pos))
    }

    fn binary_op(
        &mut self,
        func1: fn(&mut Self, &mut Scope) -> ParseResult,
        ops: Vec<TokenType>,
        func2: fn(&mut Self, &mut Scope) -> ParseResult,
        scope: &mut Scope,
    ) -> ParseResult {
        let mut left = func1(self, scope)?;
        let mut token_type = self.current_token.token_type.clone();
        while ops.contains(&token_type) {
            let op = self.current_token.clone();
            self.advance();
            let right = func2(self, scope)?;
            if [TokenType::Div, TokenType::Mod].contains(&op.token_type) {
                if let Node::Number(Token {
                    token_type: TokenType::Number(0),
                    ..
                }) = right
                {
                    return Err(Error::new(
                        ErrorType::DivisionByZero,
                        self.current_token.position.clone(),
                        "Division by zero".to_string(),
                    ));
                }
            }
            left = Node::BinaryOp(op, Box::new(left), Box::new(right));
            token_type = self.current_token.token_type.clone();
        }
        Ok(left)
    }
}

/// Parses the given vector of tokens into an AST.
/// Returns the root node of the AST.
/// # Errors
/// If the tokens cannot be parsed into an AST, an error is returned.
pub fn parse(tokens: Vec<Token>) -> ParseResult {
    let token = tokens[0].clone();
    let mut global = Scope::new(None);
    let mut obj = Parser {
        tokens,
        token_index: 0,
        current_token: token,
    };
    let ast = obj.statements(TokenType::Eof, true, &mut global)?;
    let ast = match check_undefined(&mut global) {
        Some(err) => return Err(err),
        None => ast,
    };
    match keyword_checks(&ast) {
        Some(err) => Err(err),
        None => Ok(ast),
    }
}

/// Checks for undefined functions and variables.
fn check_undefined(global: &mut Scope) -> Option<Error> {
    fn check_error(scope: &Scope) -> Option<&Error> {
        if scope.error.is_some() {
            return scope.error.as_ref();
        }
        if scope.func_error.is_some() {
            return scope.func_error.as_ref();
        }
        for child in &scope.scopes {
            if let Some(err) = check_error(child) {
                return Some(err);
            }
        }
        None
    }
    if let Some(err) = check_error(global) {
        return Some(err.clone());
    }

    fn refresh(scope: &mut Scope, parent: Scope) {
        scope.parent = Some(Box::new(parent));
        scope.refresh();
        let clone = scope.clone();
        for child in scope.scopes.iter_mut() {
            refresh(child, clone.clone());
        }
    }

    let clone = global.clone();
    for child in global.scopes.iter_mut() {
        refresh(child, clone.clone());
    }

    fn check_functions(scope: &mut Scope) -> Option<Node> {
        if !scope.unresolved_functions.is_empty() {
            return Some(scope.unresolved_functions.pop().unwrap());
        }
        for child in &mut scope.scopes {
            if let Some(err) = check_functions(child) {
                return Some(err);
            }
        }
        None
    }

    if let Some(err) = check_error(global) {
        return Some(err.clone());
    }

    if let Some(node) = check_functions(global) {
        match &node {
            Node::Call(node, _, _) => match &**node {
                Node::VarAccess(token) => {
                    return Some(Error::new(
                        ErrorType::UndefinedFunction,
                        token.position.clone(),
                        format!("Function {} is not defined", token),
                    ));
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    None
}

/// Checks for invalid placement and use of keywords
fn keyword_checks(ast: &Node) -> Option<Error> {
    fn check_return(node: &Node) -> Option<Position> {
        match node {
            Node::None(_) => None,
            Node::Number(_) => None,
            Node::Tuple(_) => None,
            Node::BinaryOp(_, n1, n2) => {
                let n1 = check_return(n1);
                if n1.is_some() {
                    return n1;
                }
                let n2 = check_return(n2);
                if n2.is_some() {
                    return n2;
                }
                None
            }
            Node::UnaryOp(_, n1) => check_return(n1),
            Node::VarAssign(_, n1, _) => check_return(n1),
            Node::VarAccess(_) => None,
            Node::VarReassign(_, n1) => check_return(n1),
            Node::Statements(..) => None,
            Node::Ternary(n1, n2, n3, _) => {
                let n1 = check_return(n1);
                if n1.is_some() {
                    return n1;
                }
                let n2 = check_return(n2);
                if n2.is_some() {
                    return n2;
                }
                let n3 = check_return(n3);
                if n3.is_some() {
                    return n3;
                }
                None
            }
            Node::If(n1, n2, n3, _) => {
                let n1 = check_return(n1);
                if n1.is_some() {
                    return n1;
                }
                let n2 = check_return(n2);
                if n2.is_some() {
                    return n2;
                }
                if let Some(n3) = n3 {
                    let n3 = check_return(n3);
                    if n3.is_some() {
                        return n3;
                    }
                }
                None
            }
            Node::Call(n1, n2, _) => {
                let n1 = check_return(n1);
                if n1.is_some() {
                    return n1;
                }
                for i in n2.iter().map(check_return) {
                    if i.is_some() {
                        return i;
                    }
                }
                None
            }
            Node::FuncDef(..) => None,
            Node::Return(_, pos) => Some(pos.clone()),
            Node::Ref(n1, _) | Node::Deref(n1, _) => check_return(n1),
            Node::Print(n1, _) | Node::Ascii(n1, _) => {
                for n in n1 {
                    if let Some(t) = check_return(n) {
                        return Some(t);
                    }
                }
                None
            }
            Node::Input(_) => None,
        }
    }
    match ast {
        Node::Statements(nodes, _) => {
            for node in nodes.iter() {
                if let Some(position) = check_return(node) {
                    return Some(Error::new(
                        ErrorType::InvalidReturn,
                        position,
                        "Return statement cannot be in the global scope".to_string(),
                    ));
                }
            }
            None
        }
        _ => unreachable!(),
    }
}
