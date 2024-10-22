use crate::ast::SourceLoc;

pub struct CompileError {
    message: String,
    r#where: SourceLoc
}

impl CompileError {
    pub fn new(message: String, r#where: &SourceLoc) -> Self {
        Self { message, r#where: r#where.clone() }
    }

    pub fn print(&self) {
        eprintln!("{} at line {}", self.message, self.r#where.line_start);
    }

    pub fn throw(message: String, r#where: &SourceLoc) -> ! {
        Self::new(message, r#where).print();
        panic!()
    }
}

pub struct RuntimeError {
    message: String,
    line: u32,
}

impl RuntimeError {
    pub fn new(message: String, line: u32) -> Box<Self> {
        Box::new(Self { message, line })
    }

    pub fn print(&self) {
        eprintln!("{} at line {}", self.message, self.line);
    }
}