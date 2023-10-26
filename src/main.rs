extern crate peg;
#[macro_use]
extern crate lazy_static;

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

lazy_static! {
    pub static ref BLANK: Expr = Expr::from(Symbol::new("System`Blank"));
    pub static ref BLANK_SEQ: Expr = Expr::from(Symbol::new("System`BlankSequence"));
    pub static ref BLANK_NULL_SEQ: Expr = Expr::from(Symbol::new("System`BlankNullSequence"));
    pub static ref BLANK_SYMS: Vec<&'static Expr> = vec![&*BLANK, &*BLANK_SEQ, &*BLANK_NULL_SEQ];
}

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
        } else if h == &Expr::symbol(Symbol::new("System`SameQ")) {
            return (es[0] == es[1]).into();
        }
    }
    ex
}

fn head(e: Expr) -> Expr {
    if let Some(h) = e.normal_head() {
        h
    } else {
        match e.kind() {
            ExprKind::Integer(_) => Expr::symbol(Symbol::new("System`Integer")),
            ExprKind::Real(_) => Expr::symbol(Symbol::new("System`Real")),
            ExprKind::Symbol(_) => Expr::symbol(Symbol::new("System`Symbol")),
            ExprKind::String(_) => Expr::symbol(Symbol::new("System`String")),
            _ => Expr::null(),
        }
    }
}

fn sym(s: &str) -> Symbol {
    Symbol::new(s)
}

fn syme(s: &str) -> Expr {
    Expr::symbol(sym(s))
}

/// we assume p.head() == &Expr::from(Symbol::new("System`Blank"))
fn is_blank_match(e: Expr, p: Expr) -> bool {
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

/// todo add an offset argument as a flag for whether to use the offset or not
fn pos_map_rebuild(pos: Vec<usize>, pat: Expr, pos_map: &HashMap<Vec<usize>, Expr>) -> Expr {
    if let Some(replacement) = pos_map.get(&pos) {
        return replacement.clone();
    }

    match pat.kind() {
        ExprKind::Normal(es) => {
            let mut new_es = vec![];

            // we need to rebuild the head separately since ExprKind::Normal keeps them separate
            let mut new_pos = pos.clone();
            new_pos.push(0);
            let new_eh = pos_map_rebuild(new_pos, es.head().clone(), pos_map);
            new_es.push(new_eh);

            for (i, e) in es.elements().iter().enumerate() {
                let mut new_pos = pos.clone();
                new_pos.push(i + 1);
                let new_e = pos_map_rebuild(new_pos, e.clone(), pos_map);
                new_es.push(new_e);
            }
            Expr::normal(new_es[0].clone(), new_es[1..].to_vec())
        }
        _ => pat,
    }
}

fn splice_sequences(expr: Expr) -> Expr {
    match expr.kind() {
        ExprKind::Normal(n) => {
            // in this version we assume that the head is not a Sequence
            let (h, es) = (n.head(), n.elements());
            let mut new_es = vec![];
            for e in es {
                let new_e = splice_sequences(e.clone());
                new_es.push(new_e);
            }

            let mut new = vec![];
            for ne in new_es {
                if let ExprKind::Normal(n) = ne.kind() {
                    let (h, es) = (n.head(), n.elements());
                    if h == &sym("System`Sequence") {
                        // we need to splice the Sequence into the list

                        new.extend_from_slice(es);
                        continue;
                    }
                }
                new.push(ne);
            }

            Expr::normal(h.clone(), new)
        }
        _ => expr,
    }
}

fn rebuild_and_splice(
    pat: Expr,
    pos: &Vec<usize>,
    pos_map: &HashMap<Vec<usize>, Expr>,
    named_map: &HashMap<Expr, Expr>,
    use_offset: bool,
) -> Expr {
    let mut new_pat = pos_map_rebuild(pos.clone(), pat.clone(), pos_map);
    new_pat = splice_sequences(new_pat);
    new_pat
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

            if BLANK_SYMS.contains(&ph) {
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

            'outer: for (i, pi) in pes.iter().enumerate() {
                let ip1 = i + 1;
                let mut new_pos = pos.clone();
                new_pos.push(ip1);
                if pi.normal_head() == Some(BLANK_SEQ.clone()) {
                    if let ExprKind::Normal(pn) = pi.kind() {
                        let (pih, pies) = (pn.head(), pn.elements());
                        // j represents the number of elements in the matched Sequence
                        // which is why we start with 1 for BLANK_SEQ and 0 for BLANK_NULL_SEQ
                        for j in 1..=ees.len() {
                            let mut elts = vec![syme("System`Sequence")];
                            // now we build up the elements of the Sequence
                            // which start at index i and go to i+j

                            if i + j > ees.len() {
                                println!("breaking news!");
                                break 'outer;
                            }

                            for k in i..(i + j) {
                                let seq_e = &ees[k];
                                if pn.elements().len() == 1 {
                                    let b_head = &pies[0];
                                    if b_head != &head(seq_e.clone()) {
                                        break;
                                    }
                                }
                                elts.push(ees[k].clone());
                            }
                            let seq = Expr::normal(elts[0].clone(), elts[1..].to_vec());
                            pos_map.insert(new_pos.clone(), seq.clone());

                            // now that we have a potential solution for the Sequence matching
                            // we need to rebuild the pattern with the Sequence replaced and recurse
                            // to see if any subsequent patterns match
                            let new_pat =
                                rebuild_and_splice(pat.clone(), &pos, pos_map, named_map, false);
                            println!("new_pat in bs: at iter {j} {new_pat}");
                            let mut copy = pos_map.clone();
                            // this is to avoid double application of a pos rule
                            copy.remove(&new_pos);

                            // now we recurse with our "guess"
                            if my_match(ctx, ex.clone(), new_pat, pos, &mut copy, named_map) {
                                pos_map.clear();
                                pos_map.extend(copy);

                                pos_map.insert(new_pos.clone(), seq.clone());

                                break 'outer;
                            } else {
                                // break 'outer;
                                // i think we need to revert pos_map to whatever it was before this my_match ctx, call
                            }
                        }
                    }
                    // }
                } else {
                    if !my_match(
                        ctx,
                        e.elements()[i].clone(),
                        pi.clone(),
                        &new_pos,
                        pos_map,
                        named_map,
                    ) {
                        break 'outer;
                    }
                }
            } // 'outer

            let final_pat = rebuild_and_splice(pat.clone(), &pos, pos_map, named_map, true);
            println!("final comparison: POS: {pos:?} | PAT: {pat} | NEW_PAT: {final_pat} | EX: {ex} || pos {pos_map:?} || named {named_map:?}");
            if final_pat == ex {
                return true;
            }
            false
        }
        (_, ExprKind::Normal(p)) => {
            if BLANK_SYMS.contains(&p.head()) {
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

fn main() -> Result<()> {
    let mut ctx = Context2 {
        vars: HashMap::new(),
    };

    let rl = setup_repl();
    let e = Expr::from(2);
    // let v = vec![1];
    // println!("{} {:?}", e, v[1..].to_vec());
    let ex = parse("(f (Sequence a b c))");
    let ex2 = splice_sequences(ex.clone());
    println!("{}", ex);
    println!("{}", ex2);
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
        Ok(expr) => evaluate(ctx, expr),
        Err(err) => panic!("Failed to parse: {s}: {err}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn head_tests() {
        assert_eq!(
            head(Expr::from(2)),
            Expr::symbol(Symbol::new("System`Integer"))
        );
        assert_eq!(
            head(Expr::real(2.0)),
            Expr::symbol(Symbol::new("System`Real"))
        );
        assert_eq!(
            head(Expr::from(Symbol::new("System`x"))),
            Expr::symbol(Symbol::new("System`Symbol"))
        );
        assert_eq!(
            head(Expr::from("Hello")),
            Expr::symbol(Symbol::new("System`String"))
        );
    }

    #[test]
    fn test_matcher() {
        let mut ctx = Context2 {
            vars: HashMap::new(),
        };

        let cases = vec![
            ("(MatchQ 1 (Blank))", parse("True")),
            ("(MatchQ 1 (Blank Integer))", parse("True")),
            ("(MatchQ (f x) (Blank))", parse("True")),
            ("(MatchQ (f x) (Blank f))", parse("True")),
        ];

        for (c, e) in cases {
            assert_eq!(ctx_evalparse(&mut ctx, c), e)
        }
    }

    #[test]
    fn test_splice() {
        // let mut ctx = Context2 {
        //     vars: HashMap::new(),
        // };

        // let cases = vec![
        //     ("(MatchQ 1 (Blank))", parse("True")),
        //     ("(MatchQ 1 (Blank Integer))", parse("True")),
        //     ("(MatchQ (f x) (Blank))", parse("True")),
        //     ("(MatchQ (f x) (Blank f))", parse("True")),
        // ];

        let ex = parse("(f (Sequence a b c))");
        let ex2 = splice_sequences(ex.clone());
        println!("{}", ex);
        println!("{}", ex2);
        // for (c, e) in cases {
        // assert_eq!(ctx_evalparse(&mut ctx, c), e)
        // }
    }
}
