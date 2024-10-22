use std::ops::Range;

use logos::{Logos, SpannedIter};

#[derive(Logos, Debug, Clone)]
#[logos(skip "[ \t]*")]
#[logos(error = LexerError)]
#[logos(extras = LineCounter)]
pub enum Token {
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
    #[regex(r"0|[1-9][0-9]*", |lex| lex.slice().parse::<i64>().unwrap())]
    Int(i64),
    #[regex(r"\r?\n\s*", newline_callback)]
    Nl,
    #[regex(r"\/\*[^*]*\*+([^/*][^*]*\*+)*\/", multiline_comment_callback)] // C-style comments
    MultiLineComment,
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
    #[token("null")]
    KwNull,
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
    #[token("?")]
    QMark,
}

fn newline_callback(lex: &mut logos::Lexer<Token>) {
    lex.slice().chars().for_each(|c| {
        if c == '\n' {
            lex.extras.line += 1;
        }
    });
    lex.extras.line_start_char = lex.span().start;
}

fn multiline_comment_callback(lex: &mut logos::Lexer<Token>) -> logos::Skip {
    // count newlines in the comment
    let st = lex.span().start;
    lex.slice().chars().enumerate().for_each(|(i, c)| {
        if c == '\n' {
            lex.extras.line += 1;
            lex.extras.line_start_char = st + i;
        }
    });
    logos::Skip
}

pub struct LineCounter {
    line: usize,
    line_start_char: usize,
}

impl std::default::Default for LineCounter {
    fn default() -> Self {
        Self { line: 1, line_start_char: 0 }
    }
}

impl LineCounter {
    pub fn get_locations(&self, span: &Range<usize>) -> (LexerLoc, LexerLoc) {
        let start = span.start + 1 - self.line_start_char;
        let end = span.end + 1 - self.line_start_char;
        (
            LexerLoc { line: self.line as u32, col: start as u32, },
            LexerLoc { line: self.line as u32, col: end as u32, },
        )
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct LexerLoc {
    pub line: u32,
    pub col: u32,
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
    type Item = Spanned<Token, LexerLoc, LexerError>;
  
    fn next(&mut self) -> Option<Self::Item> {
        let (res, span) = self.token_stream.next()?;
        match res {
            Err(err) => Some(Err(err)),
            Ok(token) => {
                let (loc1, loc2) = self.token_stream.extras.get_locations(&span);
                Some(Ok((loc1, token, loc2)))
            }
        }
    }
}
