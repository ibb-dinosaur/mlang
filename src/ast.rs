use std::{cell::RefCell, collections::HashMap, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ty {
    Unk,
    Int,
    Void,
    Bool,
    Any,
    Func(Box<Ty>, Box<[Ty]>),
    UserTy(TypeDef),
    #[allow(clippy::enum_variant_names)]
    /// Used for type inference and checking
    TyVar(usize),
    Named(String),
}

impl Ty {
    pub fn is_var(&self) -> bool {
        matches!(self, Ty::TyVar(_))
    }

    /// Primitive types
    pub fn is_primitive(&self) -> bool {
        matches!(self, Ty::Int | Ty::Void | Ty::Bool)
    }

    /// Nominal types
    pub fn is_nominal(&self) -> bool {
        self.is_primitive() || matches!(self, Ty::Named(_) | Ty::UserTy(_))
    }
}

pub enum ExprKind {
    Literal(Literal),
    Var(String),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    TypeCast(TypeCastKind, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    //FunctionCall(String, Vec<Expr>),
    // Add more expression kinds as needed
}

#[derive(Clone, PartialEq)]
pub enum Literal {
    Void,
    Int(i64),
    Bool(bool),
}

impl ExprKind {
    pub fn expr(self) -> Expr {
        Expr { ty: Ty::Unk, kind: self, extra: None }
    }

    pub fn expr_typed(self, ty: Ty) -> Expr {
        Expr { ty, kind: self, extra: None }
    }
}

pub struct Expr {
    pub ty: Ty,  // The type of the expression
    pub kind: ExprKind,   // The actual kind of expression
    /// Arbitrary extra data that can be attached to an expression during analysis
    pub extra: Option<Box<dyn std::any::Any>>,
}

impl Expr {
    pub fn set_extra<T: 'static>(&mut self, extra: T) {
        debug_assert!(self.extra.is_none());
        self.extra = Some(Box::new(extra));
    }

    pub fn get_extra<T: 'static>(&self) -> Option<&T> {
        self.extra.as_ref().and_then(|b| b.downcast_ref())
    }
}

#[derive(Clone, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    CmpEq,
    CmpNe,
    CmpLt,
    CmpLe,
    CmpGt,
    CmpGe,
}

impl BinOp {
    pub fn is_arithmetic(&self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul)
    }

    pub fn is_eq_comparison(&self) -> bool {
        matches!(self, BinOp::CmpEq | BinOp::CmpNe)
    }

    pub fn is_ord_comparison(&self) -> bool {
        matches!(self, BinOp::CmpLt | BinOp::CmpLe | BinOp::CmpGt | BinOp::CmpGe)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum TypeCastKind {
    /// Cast arbitrary type to Any, cannot fail
    ToAny,
    /// Try to cast Any to a specific simple type, fails if Any is not this exact type (simple cast, no subtyping)
    FromAnySimple,
    /// Try to cast Any to a specific function type
    FromAnyToFunc,
}

pub enum Statement {
    ExprStmt(Expr),       // Expression statement
    Return(Expr),         // Return statement
    Let(String, Expr),    // Variable declaration and assignment
    Assign(String, Expr),
    If(Expr, Vec<Statement>, Vec<Statement>)
}

pub struct Function {
    pub name: String,
    pub params: Vec<(String, Ty)>,
    pub return_type: Ty,
    pub body: Vec<Statement>,  // Multiple statements in function body
}

impl Function {
    pub fn create_ftype(&self) -> Ty {
        Ty::Func(Box::new(self.return_type.clone()), self.params.iter().map(|(_, ty)| ty.clone()).collect())
    }
}

#[derive(Debug)]
pub struct TypeDefinition {
    pub name: String,
    pub fields: Vec<(String, Ty)>
}

#[derive(Debug, Clone)]
pub struct TypeDef(Rc<RefCell<TypeDefinition>>);

impl TypeDef {
    pub fn new(def: TypeDefinition) -> Self {
        TypeDef(Rc::new(RefCell::new(def)))
    }

    pub fn get(&self) -> std::cell::Ref<'_, TypeDefinition> {
        self.0.borrow()
    }

    pub fn get_mut(&self) -> std::cell::RefMut<'_, TypeDefinition> {
        self.0.borrow_mut()
    }
}

impl PartialEq for TypeDef {
    fn eq(&self, other: &Self) -> bool {
        // there should be only one instance of each type definition
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for TypeDef {}
impl PartialOrd for TypeDef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TypeDef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.as_ptr().cmp(&other.0.as_ptr())
    }
}

pub struct Program {
    pub functions: Vec<Function>,
    pub user_types: Vec<TypeDef>,
    //pub type_map: HashMap<String, Ty>,
}

impl Program {
    pub fn new(functions: Vec<Function>, user_types: Vec<TypeDefinition>) -> Self {
        Program { functions, 
            user_types: user_types.into_iter().map(TypeDef::new).collect(), 
            /*type_map: HashMap::new()*/ }
    }
}


// Display implementations


impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::CmpEq => "==",
            BinOp::CmpNe => "!=",
            BinOp::CmpLt => "<",
            BinOp::CmpLe => "<=",
            BinOp::CmpGt => ">",
            BinOp::CmpGe => ">=",
        })
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Unk => write!(f, "unknown"),
            Ty::Int => write!(f, "int"),
            Ty::Void => write!(f, "void"),
            Ty::Bool => write!(f, "bool"),
            Ty::Any => write!(f, "any"),
            Ty::TyVar(i) => write!(f, "tv${}", i),
            Ty::Func(ret, params) => {
                write!(f, "(fun(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ") -> {})", ret)
            },
            Ty::Named(s) => write!(f, "`{}`", s),
            Ty::UserTy(ty) => write!(f, "{}", ty.get().name),
        }
    }
}

impl Expr {
    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ExprKind::Literal(Literal::Void) => write!(f, "void"),
            ExprKind::Literal(Literal::Int(i)) => write!(f, "{}", i),
            ExprKind::Literal(Literal::Bool(b)) => write!(f, "{}", b),
            ExprKind::Var(s) => write!(f, "{}:{}", s, self.ty),
            ExprKind::BinOp(op, lhs, rhs) => {
                write!(f, "(")?;
                lhs.display(f)?;
                write!(f, " {} ", op)?;
                rhs.display(f)?;
                write!(f, ")")
            },
            ExprKind::TypeCast(_, e) => {
                write!(f, "(")?;
                e.display(f)?;
                write!(f, " as {})", self.ty)
            },
            ExprKind::Call(e, args) => {
                e.display(f)?;
                write!(f, "(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    arg.display(f)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Statement {
    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::ExprStmt(e) => e.display(f),
            Statement::Return(e) => {
                write!(f, "return ")?;
                e.display(f)
            },
            Statement::Let(s, e) => {
                write!(f, "let {} = ", s)?;
                e.display(f)
            }
            Statement::Assign(s, e) => {
                write!(f, "{} = ", s)?;
                e.display(f)
            }
            Statement::If(cond, then_, else_) => {
                write!(f, "if ")?;
                cond.display(f)?;
                writeln!(f, " {{")?;
                for stmt in then_ {
                    stmt.display(f)?;
                    writeln!(f)?;
                }
                if !else_.is_empty() {
                    writeln!(f, "}} else {{")?;
                    for stmt in else_ {
                        stmt.display(f)?;
                        writeln!(f)?;
                    }
                }
                write!(f, "}}")
            }
        }
    }
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fun {}(", self.name)?;
        for (i, (name, ty)) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", name, ty)?;
        }
        writeln!(f, ") -> {} {{", self.return_type)?;
        for stmt in &self.body {
            stmt.display(f)?;
            writeln!(f)?;
        }
        writeln!(f, "}}")
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for func in &self.functions {
            writeln!(f, "{}", func)?;
        }
        Ok(())
    }
}