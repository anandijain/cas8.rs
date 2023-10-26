extern crate peg;
use std::{
    borrow::Cow::{self, Borrowed, Owned},
    ops::{Add, Mul},
};

use ordered_float::{self, NotNan};
// use rug::Integer;
// use num_bigint::BigInt;
use num_traits::cast::ToPrimitive;

use rustyline::{
    config::Configurer,
    error::ReadlineError,
    highlight::{Highlighter, MatchingBracketHighlighter},
    history::FileHistory,
    validate::MatchingBracketValidator,
    Completer, Editor, Helper, Hinter, Result, Validator,
};

use std::collections::HashMap;
use std::ops::{Deref, DerefMut};
use std::time::{Duration, Instant};
use std::{fmt, path::Path};

use wolfram_expr::{Expr, ExprKind, Normal, Number, Symbol};
// use wolfram_expr::ExprKind::Normal

#[derive(Helper, Completer, Hinter, Validator)]
pub struct ReplHelper {
    highlighter: MatchingBracketHighlighter,
    #[rustyline(Validator)]
    validator: MatchingBracketValidator,
    colored_prompt: String,
}

impl Highlighter for ReplHelper {
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        if default {
            Borrowed(&self.colored_prompt)
        } else {
            Borrowed(prompt)
        }
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Owned("\x1b[1m".to_owned() + hint + "\x1b[m")
    }

    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

pub fn run(
    mut rl: rustyline::Editor<ReplHelper, rustyline::history::FileHistory>,
    ctx: &mut Context2,
) -> Result<()> {
    let mut i = 1;

    loop {
        let prompt = format!("(In {}) := ", i);
        rl.helper_mut().expect("No helper").colored_prompt = format!("\x1b[1;32m{prompt}\x1b[0m");

        let line = rl.readline(&prompt); // read
        match line {
            Ok(l) => {
                rl.add_history_entry(l.as_str()).unwrap(); // history
                                                           // saving every line (even if slow, just until its more stable)
                rl.save_history("history.txt").unwrap();

                let exs = expr_parser::expressions(&l);

                match exs {
                    Ok(exprs) => {
                        for expr in exprs {
                            let res = evaluate(ctx, expr.clone());
                            // let res_str = format!("Out[{}] = {}", i, res);
                            println!("\x1B[1m(Out {i}) = {}\x1B[0m", res);
                            i += 1;
                        }
                    }

                    Err(err) => println!("Failed to parse: {}", err),
                }
            }
            Err(ReadlineError::Interrupted) => {
                continue;
            }
            Err(ReadlineError::Eof) => {
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
            }
        }
    } // loop
    Ok(())
}

fn setup_repl() -> Editor<ReplHelper, FileHistory> {
    let h = ReplHelper {
        highlighter: MatchingBracketHighlighter::new(),
        colored_prompt: "".to_owned(),
        validator: MatchingBracketValidator::new(),
    };
    let config = rustyline::Config::default();
    let mut rl = Editor::with_config(config).unwrap();
    rl.set_max_history_size(10000).unwrap();
    rl.set_helper(Some(h));
    if rl.load_history("history.txt").is_err() {
        println!("No previous history.");
    }
    rl
}

peg::parser! {
    grammar expr_parser() for str {
        rule comment()
            = "(*" (!"*)" [_])* "*)"

        rule whitespace() = ([' ' | '\t' | '\n' | '\r'] / comment())* // Allow whitespace or comments

        pub rule integer() -> Expr
            = n:$("-"? ['0'..='9']+ ) { Expr::from(n.parse::<i64>().unwrap()) }

        rule real() -> Expr
            = n:$("-"? ['0'..='9']* "." ['0'..='9']* ) { Expr::real(n.parse::<f64>().unwrap()) }

        rule symbol() -> Expr
            = s:$(['a'..='z' | 'A'..='Z' | '?' | '$'] ['a'..='z' | 'A'..='Z' | '0'..='9' | '-' | '_' | '`']* ) { Expr::symbol(Symbol::new(&format!("System`{}", s))) }

        rule string() -> Expr
            = "\"" s:$((!['"'][_])* ) "\"" { Expr::from(s.to_string()) }

        rule atom() -> Expr
            = symbol() / string() / real() / integer()

        rule normal() -> Expr
            = "(" h:Expr() contents:Expr()** whitespace() ")" { Expr::normal(h, contents) }

        pub rule Expr() -> Expr
            = whitespace() e:(atom() / normal()) whitespace() { e }

        pub rule expressions() -> Vec<Expr>
            = whitespace() e:Expr() ** whitespace() { e }
    }
}

fn parse(s: &str) -> Expr {
    expr_parser::Expr(s).unwrap()
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context2 {
    vars: HashMap<Expr, TableEntry>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TableEntry {
    own: Option<Expr>,
    down: Expr,
    sub: Expr,
}

impl TableEntry {
    pub fn new() -> Self {
        Self {
            own: None,
            down: Expr::list(vec![]),
            sub: Expr::list(vec![]),
        }
    }
}

/// we assume p.head() == &Expr::from(Symbol::new("System`Blank"))
fn is_blank_match(e:Expr, p:Expr) -> bool {
    if let ExprKind::Normal(ps) = p.kind() {
        let pes = ps.elements();
        if pes.len() == 1 {
            let p_head = &pes[0];
            let eh = &head(e);
            // println!("is_blank_match: {eh} | {p_head}");
            if p_head == eh {
                true
            } else {
                false
            }
        } else if pes.len() == 0 {
            true
        } else {
            println!("is_blank_match got a Blank with other than 0 or 1 elements");
            false
        }
    } else {
        panic!("is_blank_match needs a list for p")
    }
}

fn my_match(
    ctx: &mut Context2,
    ex: Expr,
    pat: Expr,
    pos: &Vec<usize>,
    pos_map: &mut HashMap<Vec<usize>, Expr>,
    named_map: &mut HashMap<Expr, Expr>,
) -> bool {
    println!("M: {pos:?} | {ex} | {pat} | {pos_map:?} | {named_map:?}");

    match (ex.kind(), pat.kind()) {
        (ExprKind::Normal(e), ExprKind::Normal(p)) => {
            let (ph, pes) = (p.head(), p.elements());
            let (eh, ees) = (e.head(), e.elements());
            if ph == &Expr::from(Symbol::new("System`Blank")) {
                if is_blank_match(ex.clone(), pat.clone()) {
                    pos_map.insert(pos.to_vec(), ex.clone());
                    return true;
                } else {
                    return false;
                }
            }
            
            let mut new_pos = pos.clone();
            new_pos.push(0);

            if !my_match(ctx, eh.clone(), ph.clone(), &new_pos, pos_map, named_map) {
                return false;
            }
            
            for (i, (ei, pi)) in e.elements().iter().zip(p.elements()).enumerate() {
                let mut new_pos = pos.clone();
                new_pos.push(i + 1);
                if !my_match(ctx, ei.clone(), pi.clone(), &new_pos, pos_map, named_map) {
                    return false;
                }
            }
            
            true
        }
        (_, ExprKind::Normal(p)) => {
            println!("non ll ");
            let eh = head(ex.clone());
            if p.head() == &Expr::from(Symbol::new("System`Blank")) {
                println!("non ll inb");
                if is_blank_match(ex.clone(), pat.clone()) {
                    pos_map.insert(pos.to_vec(), ex.clone());
                    return true;
                } else {
                    return false;
                }
            }
            false
        }
        (e, p) => e == p,
    }
}

fn evaluate(ctx: &mut Context2, ex: Expr) -> Expr {
    let mut expr = ex.clone();
    let mut last = None;
    // println!("Evaluating {}", expr);
    loop {
        // If the expression hasn't changed, break the loop.
        if Some(&expr) == last.as_ref() {
            break;
        }
        last = Some(expr.clone());

        match expr.kind() {
            ExprKind::Normal(n) => {
                let (h, es) = (n.head(), n.elements());
                let nh = evaluate(ctx, h.clone());

                let mut nes = vec![];
                for e in es {
                    let ne = evaluate(ctx, e.clone());
                    nes.push(ne);
                }
                // println!("{} {}", nh, nes.len());
                let app = internal_functions_apply(ctx, Expr::normal(nh, nes));
                // println!("App {}", app);
                expr = app;
            }
            _ => {}
        }
    }
    expr
}

pub fn internal_functions_apply(ctx: &mut Context2, ex: Expr) -> Expr {
    println!("Applying {}", ex);
    if let ExprKind::Normal(n) = ex.kind() {
        let (h, es) = (n.head(), n.elements());

        if h == &Expr::symbol(Symbol::new("System`Plus")) {
            println!("Plus");
            if let (ExprKind::Integer(a), ExprKind::Integer(b)) = (es[0].kind(), es[1].kind()) {
                let ret = Expr::from(a + b);
                println!("Integers reutrning {}", ret);
                return ret;
            }
            return ex.into();
        } else if h == &Expr::symbol(Symbol::new("System`MatchQ")) {
            return my_match(
                ctx,
                es[0].clone(),
                es[1].clone(),
                &vec![],
                &mut HashMap::new(),
                &mut HashMap::new(),
            )
            .into();
        } else if h == &Expr::symbol(Symbol::new("System`Head")) {
            return head(es[0].clone());
        }

        return ex.into();
    } else {
        ex
    }
}

fn head(e:Expr) -> Expr {
    if let Some(h) = e.normal_head() {
        h
    } else {
        match e.kind() {
            ExprKind::Integer(_) => Expr::symbol(Symbol::new("System`Integer")),
            ExprKind::Real(_) => Expr::symbol(Symbol::new("System`Real")),
            ExprKind::Symbol(_) => Expr::symbol(Symbol::new("System`Symbol")),
            ExprKind::String(_) => Expr::symbol(Symbol::new("System`String")),
            _ => Expr::null()
        }
    }
}

fn main() -> Result<()> {
    let mut ctx = Context2 {
        vars: HashMap::new(),
    };

    let rl = setup_repl();
    let e = Expr::from(2);

    run(rl, &mut ctx)
}

pub fn evalparse(s: &str) -> Expr {
    let ex = expr_parser::Expr(s);
    match ex {
        Ok(expr) => {
            let mut ctx = Context2 {
                vars: HashMap::new(),
            };
            // let mut stack = Expr::li(vec![]);
            evaluate(&mut ctx, expr)
        }
        Err(err) => panic!("Failed to parse: {s}: {err}"),
    }
}

pub fn ctx_evalparse(ctx: &mut Context2, s: &str) -> Expr {
    let ex = expr_parser::Expr(s);
    match ex {
        Ok(expr) => {
            evaluate( ctx, expr)
        }
        Err(err) => panic!("Failed to parse: {s}: {err}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn head_tests() {
        assert_eq!(head(Expr::from(2)), Expr::symbol(Symbol::new("System`Integer")));
        assert_eq!(head(Expr::real(2.0)), Expr::symbol(Symbol::new("System`Real")));
        assert_eq!(head(Expr::from(Symbol::new("System`x"))), Expr::symbol(Symbol::new("System`Symbol")));
        assert_eq!(head(Expr::from("Hello")), Expr::symbol(Symbol::new("System`String")));
    }
}
