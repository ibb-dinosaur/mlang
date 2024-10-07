use logos::{Logos, SpannedIter};

#[derive(Logos, Debug, Clone)]
#[logos(skip "[ \t]*")]
#[logos(skip "\\/\\*[^*]*\\*+([^/*][^*]*\\*+)*\\/")] // C-style comments
#[logos(error = LexerError)]
pub enum Token {
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
    #[regex(r"0|[1-9][0-9]*", |lex| lex.slice().parse::<i64>().unwrap())]
    Int(i64),
    #[regex(r"\r?\n\s*")]
    Nl,
    #[token("fun")]
    KwFun,
    #[token("return")]
    KwReturn,
    #[token("let")]
    KwLet,
    #[token("true")]
    KwTrue,
    #[token("false")]
    KwFalse,
    #[token("if")]
    KwIf,
    #[token("else")]
    KwElse,
    #[token("elseif")]
    KwElseif,
    #[token("end")]
    KwEnd,
    #[token("then")]
    KwThen,
    #[token("type")]
    KwType,
    #[token("new")]
    KwNew,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token("=")]
    Assign,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("->")]
    Arrow,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("<=")]
    Le,
    #[token(">=")]
    Ge,
    #[token("==")]
    Eq,
    #[token("!=")]
    Ne,
    #[token(".")]
    Dot,
}

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(Default, Debug, Clone, PartialEq)]
pub struct LexerError();

pub struct Lexer<'input> {
  // instead of an iterator over characters, we have a token iterator
  token_stream: SpannedIter<'input, Token>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        // the Token::lexer() method is provided by the Logos trait
        Self { token_stream: Token::lexer(input).spanned() }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Token, usize, LexerError>;
  
    fn next(&mut self) -> Option<Self::Item> {
      self.token_stream
        .next()
        .map(|(token, span)| Ok((span.start, token?, span.end)))
    }
}
