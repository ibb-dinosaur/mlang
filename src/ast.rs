#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ty {
    Unk,
    Int,
    Void,
    Any,
    Func(Box<Ty>, Box<[Ty]>),
    #[allow(clippy::enum_variant_names)]
    /// Used for type inference and checking
    TyVar(usize),
}

impl Ty {
    pub fn is_var(&self) -> bool {
        matches!(self, Ty::TyVar(_))
    }

    /// Simple types are: not type variables, not compound types
    pub fn is_simple(&self) -> bool {
        matches!(self, Ty::Int | Ty::Void | Ty::Any)
    }

    pub fn is_func(&self) -> bool {
        matches!(self, Ty::Func(_, _))
    }
}

#[derive(Clone, PartialEq)]
pub enum ExprKind {
    IntLiteral(i64),
    Var(String),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    TypeCast(TypeCastKind, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    //FunctionCall(String, Vec<Expr>),
    // Add more expression kinds as needed
}

impl ExprKind {
    pub fn expr(self) -> Expr {
        Expr { ty: Ty::Unk, kind: self }
    }

    pub fn expr_typed(self, ty: Ty) -> Expr {
        Expr { ty, kind: self }
    }
}

#[derive(Clone, PartialEq)]
pub struct Expr {
    pub ty: Ty,  // The type of the expression
    pub kind: ExprKind,   // The actual kind of expression
}

#[derive(Clone, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
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

#[derive(Clone, PartialEq)]
pub enum Statement {
    ExprStmt(Expr),       // Expression statement
    Return(Expr),         // Return statement
    Let(String, Expr),    // Variable declaration and assignment
    Assign(String, Expr),
}

#[derive(Clone, PartialEq)]
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

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
        })
    }
}

impl std::fmt::Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Unk => write!(f, "unknown"),
            Ty::Int => write!(f, "int"),
            Ty::Void => write!(f, "void"),
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
        }
    }
}

impl Expr {
    fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ExprKind::IntLiteral(i) => write!(f, "{}", i),
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

#[derive(Clone)]
pub struct Program {
    pub functions: Vec<Function>,
}

impl Program {
    pub fn new() -> Self {
        Program { functions: vec![] }
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