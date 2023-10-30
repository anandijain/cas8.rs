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

use wolfram_expr::{Expr, ExprKind, Symbol};

lazy_static! {
    pub static ref BLANK: Expr = Expr::from(Symbol::new("System`Blank"));
    pub static ref BLANK_SEQ: Expr = Expr::from(Symbol::new("System`BlankSequence"));
    pub static ref BLANK_NULL_SEQ: Expr = Expr::from(Symbol::new("System`BlankNullSequence"));
    pub static ref BLANK_SEQ_SYMS: Vec<&'static Expr> = vec![&*BLANK_SEQ, &*BLANK_NULL_SEQ];
    pub static ref BLANK_SYMS: Vec<&'static Expr> = vec![&*BLANK, &*BLANK_SEQ, &*BLANK_NULL_SEQ];
    pub static ref PATTERN: Expr = Expr::from(Symbol::new("System`Pattern"));
    pub static ref HOLD_PATTERN: Expr = Expr::from(Symbol::new("System`HoldPattern"));
    pub static ref SEQUENCE: Expr = Expr::from(Symbol::new("System`Sequence"));
    pub static ref MATCHQ: Expr = Expr::from(Symbol::new("System`MatchQ"));
    pub static ref HEAD: Expr = Expr::from(Symbol::new("System`Head"));
    pub static ref PLUS: Expr = Expr::from(Symbol::new("System`Plus"));
    pub static ref SET: Expr = Expr::from(Symbol::new("System`Set"));
    pub static ref SET_DELAYED: Expr = Expr::from(Symbol::new("System`SetDelayed"));
    pub static ref RULE_DELAYED: Expr = Expr::from(Symbol::new("System`RuleDelayed"));
    pub static ref RULE: Expr = Expr::from(Symbol::new("System`Rule"));
    pub static ref REPLACE: Expr = Expr::from(Symbol::new("System`Replace"));
    pub static ref REPLACE_ALL: Expr = Expr::from(Symbol::new("System`ReplaceAll"));
    pub static ref REPLACE_REPEATED: Expr = Expr::from(Symbol::new("System`ReplaceRepeated"));
    pub static ref LIST: Expr = Expr::from(Symbol::new("System`List"));
    pub static ref ATTRIBUTES: Expr = Expr::from(Symbol::new("System`Attributes"));
    pub static ref HOLD: Expr = Expr::from(Symbol::new("System`Hold"));
    pub static ref HOLD_ALL: Expr = Expr::from(Symbol::new("System`HoldAll"));
    pub static ref HOLD_FIRST: Expr = Expr::from(Symbol::new("System`HoldFirst"));
    pub static ref HOLD_REST: Expr = Expr::from(Symbol::new("System`HoldRest"));
    pub static ref HOLD_ALL_COMPLETE: Expr = Expr::from(Symbol::new("System`HoldAllComplete"));
    pub static ref FAILED: Expr = Expr::from(Symbol::new("System`$Failed"));
    pub static ref TABLE: Expr = Expr::from(Symbol::new("System`Table"));
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
    // I wonder if we should store symbols on lhs
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

// used to add an element to a list, sice we dont have deref on Expr we cant call .push()
// used in adding downvalues
// fn push_normal(ex:Expr, new:Expr) -> Expr {
//     if let ExprKind::Normal(n) = ex {
//         let (nh, es) = (n.head(), n.elements());

//         // assert_eq!(nh, &Expr::symbol(Symbol::new("System`List")));
//     }
// }

fn set(ctx: &mut Context2, ex: Expr) -> Expr {
    // the head is either Set or SetDelayed and we eiter return rhs or Null respectively
    // supported cases.
    // ownvalue
    // downvalue
    // subvalue

    // seems like relying on tag() doesn't tell us which one we're doing

    // general strat, once we've determined which Value case it is, we dont need to continue recursing
    // so once we know its a subvalue we can just store the rule
    // examples
    // (Set x 1)
    // (Set (f x) 1)
    // (Set ((k x) y) 1)

    // maybe its finally time to create insertion order too
    if let ExprKind::Normal(n) = ex.kind() {
        let (h, es) = (n.head(), n.elements());
        let is_delayed = h == &*SET_DELAYED;
        println!("set: {h} | is_delayed: {is_delayed}");
        let (lhs, rhs) = (es[0].clone(), es[1].clone());
        if let Some(t) = lhs.tag() {
            match lhs.kind() {
                // own
                ExprKind::Symbol(s) => {
                    let mut te = TableEntry::new();
                    te.own = Some(es[1].clone());
                    ctx.vars.insert(t.clone().into(), te);
                    println!("ownvalue: {t:?} | {rhs}");
                    if is_delayed {
                        return Expr::null();
                    }
                    return es[1].clone();
                }
                // down/sub
                ExprKind::Normal(n) => {
                    let (nh, nes) = (n.head(), n.elements());
                    match nh.kind() {
                        ExprKind::Symbol(nhs) => {
                            let te: &mut TableEntry = ctx
                                .vars
                                .entry(nhs.clone().into())
                                .or_insert_with(TableEntry::new);
                            let hp = Expr::normal(HOLD_PATTERN.clone(), vec![lhs.clone()]);
                            let dv = Expr::normal(RULE_DELAYED.clone(), vec![hp, rhs.clone()]);
                            // let dv_str = format!("(System`RuleDelayed (System`HoldPattern {lhs}) {rhs})");
                            // let dv = expr_parser::Expr(&dv_str).unwrap();

                            // NOTE! here we aren't inserting in the right order, where we look for more specific
                            // definitions and insert them first. so user has to do the right order themselves
                            // at the moment
                            let d = &mut te.down;
                            if let ExprKind::Normal(dn) = d.kind_mut() {
                                let mut des = dn.clone().into_elements();
                                des.push(dv);
                                te.down = Expr::normal(dn.head().clone(), des);
                                if is_delayed {
                                    return Expr::null();
                                }
                                return rhs.clone();
                            } else {
                                panic!("non Normal downvalue???")
                            }
                        }
                        _ => todo!("subval"),
                    }
                }
                _ => {
                    println!("set takes a symbol or list, got {}", lhs);
                    if is_delayed {
                        return Expr::symbol(Symbol::new("System`$Failed"));
                    }
                    return rhs;
                }
            }
        } else {
            println!("set takes a symbol or list, got {}", lhs);
            if is_delayed {
                return Expr::symbol(Symbol::new("System`$Failed"));
            }
            return rhs;
        }
    } else {
        panic!()
    }
}

fn table(ctx: &mut Context2, ex: Expr) -> Expr {
    if let ExprKind::Normal(n) = ex.kind() {
        let (h, es) = (n.head(), n.elements());
        let table_body = &es[0];

        // todo: test if this works implemented in cas3 code
        if es.len() == 1 {
            return table_body.clone();
        }
        let spec = evaluate(ctx, es[1].clone());

        if es.len() == 2 {
            // if int, we copy n times
            if let ExprKind::Integer(n) = spec.kind() {
                return Expr::list((0..n.to_i64().unwrap()).map(|_| es[0].clone()).collect());
            } else if let ExprKind::Normal(ls) = spec.kind() {
                let (lh, les) = (ls.head(), ls.elements());
                // this is the place where we want to make helpers for
                // the "standard Wolfram Language iteration specification"

                // let mut res = Expr::List(vec![sym("List")]);

                let mut res = vec![];
                let var = &les[0];

                // this specific case is {i, imax}
                if les.len() == 2 {
                    if lh != &*LIST {
                        dbg!("invalid range specification. need a list");
                        // return reconstructed_ex;
                    }

                    if let ExprKind::Integer(imax) = les[1].kind() {
                        for i in 1..=*imax {
                            // let mut e_i = Expr::List(vec![sym("replace_all")]);
                            let mut eiv = vec![];
                            eiv.push(table_body.clone());
                            let local_rule = Expr::rule(var.clone(), i.into()); // (rule var iter)
                            eiv.push(local_rule);
                            let e_i = Expr::normal(REPLACE_ALL.clone(), eiv);
                            res.push(e_i);
                        }
                        return Expr::list(res);
                    } else if let ExprKind::Normal(vals) = les[1].kind() {
                        // this is the sequence case where you just
                        // Table[expr,{i,{i1,i2,…}}]

                        if vals.head() != &*LIST {
                            dbg!(
                                "invalid range specification. need a list of values, gave {}",
                                vals
                            );
                            // return reconstructed_ex;
                        } else {
                            for val in vals.elements() {
                                let mut eiv = vec![];
                                eiv.push(table_body.clone());
                                let local_rule = Expr::rule(var.clone(), val.clone()); // (rule var iter)
                                eiv.push(local_rule);
                                let e_i = Expr::normal(REPLACE_ALL.clone(), eiv);
                                res.push(e_i);
                            }
                            return Expr::list(res);
                        }
                    } else {
                        dbg!("need an int or list for imax, reals not supported in iteration specification yet");
                        return FAILED.clone();
                    }
                } else if les.len() == 3 {
                    // this is {i, imin, imax}
                    if let (ExprKind::Integer(imin), ExprKind::Integer(imax)) =
                        (les[1].kind(), les[2].kind())
                    {
                        for i in *imin..=*imax {
                            let mut eiv = vec![];
                            eiv.push(table_body.clone());
                            let local_rule = Expr::rule(var.clone(), i.into()); // (rule var iter)
                            eiv.push(local_rule);
                            let e_i = Expr::normal(REPLACE_ALL.clone(), eiv);
                            res.push(e_i);
                        }
                        return Expr::list(res);
                    } else {
                        // this is the sequence case where you just
                        // Table[expr,{i,{i1,i2,…}}]
                        dbg!("need an int or list for imax, reals not supported in iteration specification yet");
                        return FAILED.clone();
                    }
                } else if les.len() == 4 {
                    // this is {i, imin, imax, di}
                    if let [ExprKind::Integer(imin), ExprKind::Integer(imax), ExprKind::Integer(di)] =
                        [les[1].kind(), les[2].kind(), les[3].kind()]
                    {
                        let rng = *imin..=*imax;
                        let iter = rng.step_by(*di as usize);
                        for i in iter {
                            let mut eiv = vec![];
                            eiv.push(table_body.clone());
                            let local_rule = Expr::rule(var.clone(), i.into()); // (rule var iter)
                            eiv.push(local_rule);
                            let e_i = Expr::normal(REPLACE_ALL.clone(), eiv);
                            res.push(e_i);
                        }
                        return Expr::list(res);
                    } else {
                        // this is the sequence case where you just
                        // Table[expr,{i,{i1,i2,…}}]
                        dbg!("need an int or list for imax, reals not supported in iteration specification yet");
                        return FAILED.clone();
                    }
                }
            }
        }

        // let range_lists = &es[1..]; //.clone().reverse();
        //                             // Table[ f[i,j], {i, imin, imax}, {j, jmin, jmax}]
        //                             // Table[Table[f[i,j], {j, jmin, jmax}], {i, imin, imax}]
        //                             // let mut ex = Expr::List(vec![sym("Table")]);
        //                             // ex.push(table_body.clone());

        // let mut nested_table = table_body.clone();
        // for range in range_lists.iter().rev() {
        //     let mut new_table = Expr::normal(sym("System`Table"), vec![nested_table.clone()]);
        //     new_table = match &mut new_table.kind_mut() {
        //         ExprKind::Normal(ref mut v) => {
        //             v.push(range.clone());
        //             new_table.clone()
        //         }
        //         _ => panic!("Unexpected expression type"),
        //     };
        //     nested_table = new_table;
        // }
        // return nested_table;
        panic!()
    } else {
        panic!()
    }
}

pub fn internal_functions_apply(ctx: &mut Context2, ex: Expr) -> Expr {
    // println!("Applying {}", ex);
    if let ExprKind::Normal(n) = ex.kind() {
        let (h, es) = (n.head(), n.elements());
        // right now these basic arithmetic ops aren't variadic
        if h == &Expr::symbol(Symbol::new("System`Plus")) {
            // println!("Plus");
            if let (ExprKind::Integer(a), ExprKind::Integer(b)) = (es[0].kind(), es[1].kind()) {
                let ret = Expr::from(a + b);
                // println!("Integers reutrning {}", ret);
                return ret;
            }
            return ex.into();
        } else if h == &Expr::symbol(Symbol::new("System`Times")) {
            // println!("Plus");
            if let (ExprKind::Integer(a), ExprKind::Integer(b)) = (es[0].kind(), es[1].kind()) {
                let ret = Expr::from(a * b);
                // println!("Integers reutrning {}", ret);
                return ret;
            }
            return ex.into();
        } else if h == &Expr::symbol(Symbol::new("System`MatchQ")) {
            return my_match(
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
        } else if h == &*SET || h == &*SET_DELAYED {
            return set(ctx, ex);
        } else if h == &*REPLACE {
            println!("replace");
            return replace(&es[0], &es[1]);
        } else if h == &*REPLACE_ALL {
            return replace_all(&es[0], &es[1]);
        } else if h == &*REPLACE_REPEATED {
            return replace_repeated(&es[0], &es[1]);
        } else if h == &*TABLE {
            return table(ctx, ex);
        } else if h == &Expr::symbol(Symbol::new("System`dump")) {
            println!("{:?}", ctx.vars);
            return Expr::null();
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

fn get_attributes(ctx: &mut Context2, nh: Expr) -> Expr {
    let mut nh_attrs = Expr::list(vec![]);
    // #16 - this is what we need to speed up. ideally bypass the pattern matcher somehow
    // we know/can assume we are looking up (attrs SYM)
    if let ExprKind::Symbol(_) = nh.kind() {
        let te = ctx
            .vars
            .entry(ATTRIBUTES.clone())
            .or_insert_with(TableEntry::new);
        // (down_values attrs)
        let dvs = &te.down;
        let attr_expr = Expr::normal(ATTRIBUTES.clone(), vec![nh.clone()]);
        // println!("attr_expr: {}", attr_expr);
        if let ExprKind::Normal(_ls) = dvs.kind() {
            // dv expected to be (rule_delayed (hold_pattern lhs) rhs)
            for dv in _ls.elements() {
                if let ExprKind::Normal(dvn) = dv.kind() {
                    if let ExprKind::Normal(hpn) = dvn.elements()[0].kind() {
                        let lhs = hpn.elements()[0].clone();
                        if lhs == attr_expr {
                            nh_attrs = replace(&attr_expr, dv);
                            break; // Exit the loop once a match is found
                        }
                    }
                }
            }
        } else {
            panic!("down_values must be a list");
        }
    }

    nh_attrs
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
                // println!("nh_attrs: {}", nh_attrs);
                let nh_attrs_vec =
                    if let ExprKind::Normal(nh_attrsn) = get_attributes(ctx, nh.clone()).kind() {
                        nh_attrsn.clone().into_elements()
                    } else {
                        vec![]
                    };
                // step 7
                if nh_attrs_vec.contains(&HOLD_ALL_COMPLETE) {
                    // skip to 14
                    todo!();
                }
                // hold_mask entry with a zero means "don't hold"
                let mut hold_mask = vec![false; es.len()];

                // idk if it should be else ifs
                if nh_attrs_vec.contains(&HOLD_ALL) {
                    hold_mask.fill(true);
                }
                if nh_attrs_vec.contains(&HOLD_FIRST) {
                    hold_mask[0] = true;
                }
                if nh_attrs_vec.contains(&HOLD_REST) {
                    hold_mask[1..].fill(true);
                }
                // println!("hold_mask: {:?}", hold_mask);

                let mut nes = vec![];
                for (i, e) in es.iter().enumerate() {
                    if hold_mask[i] {
                        nes.push(e.clone());
                    } else {
                        let ne = evaluate(ctx, e.clone());
                        nes.push(ne);
                    }
                }
                let reconstructed_ex = Expr::normal(nh.clone(), nes.clone());
                println!("reconstructed_ex: {}", reconstructed_ex);

                // step 14: apply user defined downvalues and subvalues
                let exprime = match nh.kind() {
                    // we dont need to panic here "abc"[foo] doesn't
                    ExprKind::Integer(_) | ExprKind::Real(_) | ExprKind::String(_) => {
                        // note: WL doesn't give note in this case
                        println!("head must be a symbol, got {nh}");
                        return reconstructed_ex;
                    }
                    // this is the down_value case, bcause the head
                    ExprKind::Symbol(_) => {
                        let te = ctx.vars.entry(nh.clone()).or_insert_with(TableEntry::new);
                        let dvs = &te.down;
                        // println!("looking for user defined down_values for {} -> {}", nh, dvs);

                        // should this be replace_all? or replace_repeated?

                        let exprime = replace_all(&reconstructed_ex, dvs);
                        // println!("before: {}", reconstructed_ex);
                        // println!("after: {}", exprime);
                        exprime
                    }
                    // subvalue
                    ExprKind::Normal(_) => reconstructed_ex.clone(),
                };

                // im not sure if this is correct, but it seems necesary,
                // if we found a matching downvalue rule, then we need to re-evaluate the expression after replacement
                if expr != exprime {
                    expr = exprime;
                    continue;
                }

                // note now that ex is not necesarily a List anymore
                // so if we still have a list, then we do step 15, and apply internal down/subvalues

                match expr.kind() {
                    ExprKind::Normal(_) => {}
                    _ => continue,
                }

                // println!("{} {}", nh, nes.len());
                let app = internal_functions_apply(ctx, Expr::normal(nh, nes));
                // println!("App {}", app);
                expr = app;
            }
            ExprKind::Symbol(s) => {
                if let Some(te) = ctx.vars.get(&s.clone().into()) {
                    if let Some(own) = &te.own {
                        expr = own.clone();
                    }
                    //  else {
                    //     expr = te.down.clone();
                    // }
                }
                //  else {
                //     expr = expr.into();
                // }
            }
            _ => {}
        }
    }
    expr
}

pub fn bindings_to_rules(bindings: &HashMap<String, Expr>) -> Expr {
    let mut es = vec![];
    for (name, binding) in bindings.clone() {
        let r = Expr::rule(syme(&name), binding.clone());
        es.push(r);
    }
    Expr::list(es)
}

pub fn pat_bindings_to_rules(bindings: &HashMap<Expr, Expr>) -> Expr {
    // let mut rules = Expr::List(vec![sym("List")]);
    let mut es = vec![];

    for (pat, binding) in bindings.clone() {
        if let ExprKind::Normal(ps) = pat.kind() {
            let (psh, pses) = (ps.head(), ps.elements());
            assert_eq!(psh.clone(), syme("System`Pattern"));
            let r = Expr::rule(pses[0].clone(), binding.clone());
            es.push(r);
        }
    }
    Expr::list(es)
}

pub fn norm_rules(rules: &Expr) -> Vec<Expr> {
    let rh = head(rules.clone());
    if rh == *RULE || rh == *RULE_DELAYED {
        return vec![rules.clone()];
    } else {
        if let ExprKind::Normal(rn) = rules.kind() {
            assert_eq!(rh, *LIST);
            return rn.clone().into_elements();
        } else {
            panic!("non Normal rules ya bish")
        }
    };
}

pub fn replace(expr: &Expr, rules: &Expr) -> Expr {
    let rules_list = norm_rules(rules);
    let mut ctx = Context2 {
        vars: HashMap::new(),
    };
    for rule in rules_list {
        let pos = vec![];
        let mut pos_map = HashMap::new();
        let mut named_map = HashMap::new();
        let rh = head(rule.clone());
        assert!(rh == *RULE || rh == *RULE_DELAYED);
        if let ExprKind::Normal(rn) = rule.kind() {
            if my_match(
                expr.clone(),
                rn.elements()[0].clone(),
                &pos,
                &mut pos_map,
                &mut named_map,
            ) {
                let mut new_expr = rn.elements()[1].clone();
                new_expr = replace_all(&new_expr, &pat_bindings_to_rules(&named_map));

                return new_expr;
            }
        } else {
            panic!("non Normal rules ya bish")
        }
    }
    expr.clone()
}

pub fn replace_all(expr: &Expr, rules: &Expr) -> Expr {
    let rules_list = norm_rules(rules);
    let mut ctx = Context2 {
        vars: HashMap::new(),
    };
    for rule in rules_list {
        let pos = vec![];
        let mut pos_map = HashMap::new();
        let mut named_map = HashMap::new();
        let rh = head(rule.clone());
        println!("replace_all: {expr} | {rules} | {rh}");
        assert!(rh == *RULE || rh == *RULE_DELAYED);
        if let ExprKind::Normal(rn) = rule.kind() {
            if my_match(
                expr.clone(),
                rn.elements()[0].clone(),
                &pos,
                &mut pos_map,
                &mut named_map,
            ) {
                return replace(expr, &rule);
            }
        } else {
            panic!("non Normal rules ya bish")
        }
    }

    match expr.kind() {
        ExprKind::Normal(list) => {
            // list.
            let (lh, es) = (list.head(), list.elements());
            let mut v = vec![];
            let nh = replace_all(lh, rules);

            for e in es {
                v.push(replace_all(e, rules));
            }

            Expr::normal(nh, v)
        }
        _ => replace(expr, rules),
    }
}

pub fn replace_repeated(expr: &Expr, rules: &Expr) -> Expr {
    let mut current_expr = expr.clone();
    let mut i = 0;
    loop {
        let new_expr = replace_all(&current_expr, rules);
        if new_expr == current_expr {
            break;
        }
        current_expr = new_expr;
        i += 1;
        if i > 1 << 16 {
            println!("replace_repeated, iteration limit 1<<16 reached");
            break;
        }
    }
    current_expr
}

/// PATTERN MATCHER

/// todo add an offset argument as a flag for whether to use the offset or not
fn pos_map_rebuild(
    pos: Vec<usize>,
    pat: Expr,
    pos_map: &HashMap<Vec<usize>, Expr>,
    use_offset: bool,
) -> Expr {
    if let Some(replacement) = pos_map.get(&pos) {
        return replacement.clone();
    }

    match pat.kind() {
        ExprKind::Normal(es) => {
            let mut new_es = vec![];

            // we need to rebuild the head separately since ExprKind::Normal keeps them separate
            let mut new_pos = pos.clone();
            new_pos.push(0);
            let new_eh = pos_map_rebuild(new_pos, es.head().clone(), pos_map, use_offset);
            new_es.push(new_eh);
            let mut offset: isize = 0;

            for (i, e) in es.elements().iter().enumerate() {
                let mut new_pos = pos.clone();
                let pos_in_list = if use_offset {
                    i as isize + 1 + offset
                } else {
                    i as isize + 1
                };
                println!("iterating in pos_map_rebuild i: {i} | e: {e} | offset {offset}");
                new_pos.push(pos_in_list as usize);
                let new_e = pos_map_rebuild(new_pos, e.clone(), pos_map, use_offset);
                if let ExprKind::Normal(n) = new_e.kind() {
                    if n.head() == &syme("System`Sequence") {
                        let ne = n.elements().len();
                        // zero is because we special cased empty seqs to not splice
                        if ne == 0 {
                        } else {
                            offset += n.elements().len() as isize - 1;
                        }
                    }
                }

                new_es.push(new_e);
            }
            Expr::normal(new_es[0].clone(), new_es[1..].to_vec())
        }
        _ => pat,
    }
}

fn named_rebuild_all(expr: Expr, map: &HashMap<Expr, Expr>) -> Expr {
    // First, check if the entire expression exists in the map and replace it if it does
    if let Some(replacement) = map.get(&expr) {
        return replacement.clone();
    }

    // If the expression is not in the map, proceed with the recursion
    match expr.kind() {
        ExprKind::Normal(list) => {
            let (lh, es) = (list.head(), list.elements());
            let nh = named_rebuild_all(lh.clone(), map);
            // Recursively rebuild all sub-expressions in the list
            let new_list: Vec<Expr> = es
                .into_iter()
                .map(|e| named_rebuild_all(e.clone(), map))
                .collect();
            Expr::normal(nh, new_list)
        }
        _ => expr,
    }
}

fn splice_sequences(expr: Expr, use_offset: bool) -> Expr {
    match expr.kind() {
        ExprKind::Normal(n) => {
            // in this version we assume that the head is not a Sequence
            let (h, es) = (n.head(), n.elements());
            let mut new_es = vec![];
            for e in es {
                let new_e = splice_sequences(e.clone(), use_offset);
                new_es.push(new_e);
            }

            let mut new = vec![];
            for ne in new_es {
                if let ExprKind::Normal(n) = ne.kind() {
                    let (h, es) = (n.head(), n.elements());
                    if h == &sym("System`Sequence") {
                        if !use_offset && es.is_empty() {
                            new.push(ne);
                            continue;
                        }
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
    let mut new_pat = pos_map_rebuild(pos.clone(), pat.clone(), pos_map, use_offset);
    println!("rebuild_and_splice: {pos:?} | {pat} newpat {new_pat} | {pos_map:?} | {named_map:?} | {use_offset}", pos = pos, pat = pat, pos_map = pos_map, named_map = named_map, use_offset = use_offset);
    new_pat = named_rebuild_all(new_pat, named_map);
    new_pat = splice_sequences(new_pat, use_offset);
    println!("POST SPLICE {new_pat}");
    new_pat
}

fn my_match(
    // ctx: &mut Context2,
    ex: Expr,
    mut pat: Expr,
    pos: &Vec<usize>,
    pos_map: &mut HashMap<Vec<usize>, Expr>,
    named_map: &mut HashMap<Expr, Expr>,
) -> bool {
    // i feel like this should be moved outside of my_match
    let pattern_expr = pat.clone();
    if head(pattern_expr.clone()) == *HOLD_PATTERN {
        if let ExprKind::Normal(pn) = pattern_expr.kind() {
            pat = pn.elements()[0].clone();
        }
    }
    // println!("M: {pos:?} | {ex} | {pat} | {pos_map:?} | {named_map:?}");

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
            } else if ph == &*PATTERN {
                let b = pes[1].clone();
                if is_blank_match(ex.clone(), b) {
                    if let Some(from_map) = named_map.get(&pat) {
                        return from_map == &ex;
                    } else {
                        // doing both idk why
                        named_map.insert(pat.clone(), ex.clone());
                        pos_map.insert(pos.to_vec(), ex.clone());
                        return true;
                    }
                } else {
                    return false;
                }
            }

            let mut new_pos = pos.clone();
            new_pos.push(0);

            if !my_match(eh.clone(), ph.clone(), &new_pos, pos_map, named_map) {
                return false;
            }

            let mut num_empty_bns = 0;
            'outer: for (i, pi) in pes.iter().enumerate() {
                let ip1 = i + 1;
                let mut new_pos = pos.clone();
                new_pos.push(ip1);

                // here we do a check for empty sequence and skip
                if let ExprKind::Normal(pn) = pi.kind() {
                    // let pih = pn.head();
                    let (pih, pies) = (pn.head(), pn.elements());

                    if pih == &Expr::from(SEQUENCE.clone()) && pies.is_empty() {
                        println!("found empty sequence at {new_pos:?}");
                        num_empty_bns += 1;
                        continue;
                    }
                }

                let v = vec![Some(BLANK_SEQ.clone()), Some(BLANK_NULL_SEQ.clone())];
                if pi.normal_head() == Some(PATTERN.clone()) {
                    if let ExprKind::Normal(pn) = pi.kind() {
                        let (pih, pies) = (pn.head(), pn.elements());
                        let b = pies[1].clone();
                        if let ExprKind::Normal(bn) = b.kind() {
                            let (bnh, bnes) = (bn.head(), bn.elements());
                            //
                            if BLANK_SEQ_SYMS.contains(&bnh) {
                                let bounds = if bnh == &*BLANK_SEQ {
                                    1..=ees.len()
                                } else {
                                    0..=ees.len()
                                };

                                for j in bounds {
                                    let mut elts = vec![syme("System`Sequence")];
                                    // now we build up the elements of the Sequence
                                    // which start at index i and go to i+j

                                    if i + j - num_empty_bns > ees.len() {
                                        println!("breaking news!");
                                        break 'outer;
                                    }

                                    for k in i..(i + j) {
                                        let seq_e = &ees[k - num_empty_bns];
                                        // println!("seq_e {seq_e} | bnes {bnes}");
                                        if bnes.len() == 1 {
                                            if bnes[0] != head(seq_e.clone()) {
                                                break;
                                            }
                                        }
                                        elts.push(seq_e.clone());
                                    }

                                    let seq = Expr::normal(elts[0].clone(), elts[1..].to_vec());
                                    pos_map.insert(new_pos.clone(), seq.clone());
                                    named_map.insert(pi.clone(), seq.clone());

                                    // now that we have a potential solution for the Sequence matching
                                    // we need to rebuild the pattern with the Sequence replaced and recurse
                                    // to see if any subsequent patterns match
                                    let new_pat = rebuild_and_splice(
                                        pat.clone(),
                                        &pos,
                                        pos_map,
                                        named_map,
                                        false,
                                    );
                                    // if bnh == &*BLANK_SEQ {
                                    //     println!("new_pat in NAMED BS: seq: {seq} at iter {j} newpos {new_pos:?} {new_pat}");
                                    // } else {
                                    //     println!("new_pat in NAMED BNS: seq: {seq} at iter {j} newpos {new_pos:?} {new_pat}");
                                    // }
                                    let mut copy = pos_map.clone();
                                    // this is to avoid double application of a pos rule
                                    copy.remove(&new_pos);

                                    // now we recurse with our "guess"
                                    if my_match(ex.clone(), new_pat, pos, &mut copy, named_map) {
                                        pos_map.clear();
                                        pos_map.extend(copy);

                                        pos_map.insert(new_pos.clone(), seq.clone());

                                        break 'outer;
                                    } else {
                                        // break 'outer;
                                        // i think we need to revert pos_map to whatever it was before this my_match ctx, call
                                    }
                                }
                            } else {
                                if !my_match(
                                    e.elements()[i - num_empty_bns].clone(),
                                    pi.clone(),
                                    &new_pos,
                                    pos_map,
                                    named_map,
                                ) {
                                    break 'outer;
                                }
                            }
                        } else {
                            panic!("invalid patern. Blank needs to be Normal")
                        }
                    } else {
                        panic!("something very wrong ");
                    }
                } else if v.contains(&pi.normal_head()) {
                    if let ExprKind::Normal(pn) = pi.kind() {
                        let (pih, pies) = (pn.head(), pn.elements());

                        // j represents the number of elements in the matched Sequence
                        // which is why we start with 1 for BLANK_SEQ and 0 for BLANK_NULL_SEQ
                        let bounds = if pih == &*BLANK_SEQ {
                            1..=ees.len()
                        } else {
                            0..=ees.len()
                        };

                        for j in bounds {
                            let mut elts = vec![syme("System`Sequence")];
                            // now we build up the elements of the Sequence
                            // which start at index i and go to i+j

                            if i + j - num_empty_bns > ees.len() {
                                println!("breaking news!");
                                break 'outer;
                            }

                            for k in i..(i + j) {
                                let seq_e = &ees[k - num_empty_bns];
                                if pn.elements().len() == 1 {
                                    let b_head = &pies[0];
                                    if b_head != &head(seq_e.clone()) {
                                        break;
                                    }
                                }
                                elts.push(seq_e.clone());
                            }
                            let seq = Expr::normal(elts[0].clone(), elts[1..].to_vec());
                            pos_map.insert(new_pos.clone(), seq.clone());

                            // now that we have a potential solution for the Sequence matching
                            // we need to rebuild the pattern with the Sequence replaced and recurse
                            // to see if any subsequent patterns match
                            let new_pat =
                                rebuild_and_splice(pat.clone(), &pos, pos_map, named_map, false);
                            // if pih == &*BLANK_SEQ {
                            //     println!("new_pat in BS: seq: {seq} at iter {j} newpos {new_pos:?} {new_pat}");
                            // } else {
                            //     println!("new_pat in BNS: seq: {seq} at iter {j} newpos {new_pos:?} {new_pat}");
                            // }
                            let mut copy = pos_map.clone();
                            // this is to avoid double application of a pos rule
                            copy.remove(&new_pos);

                            // now we recurse with our "guess"
                            if my_match(ex.clone(), new_pat, pos, &mut copy, named_map) {
                                pos_map.clear();
                                pos_map.extend(copy);

                                pos_map.insert(new_pos.clone(), seq.clone());

                                break 'outer;
                            } else {
                                // break 'outer;
                                // i think we need to revert pos_map to whatever it was before this my_match ctx, call
                            }
                        }
                    } else {
                        panic!("something very wrong ");
                    }
                } else {
                    let eelts = e.elements();
                    let ex_idx = i - num_empty_bns;
                    if ex_idx >= eelts.len() {
                        break 'outer;
                    }
                    if !my_match(
                        eelts[ex_idx].clone(),
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
            // println!("final comparison: POS: {pos:?} | PAT: {pat} | NEW_PAT: {final_pat} | EX: {ex} || pos {pos_map:?} || named {named_map:?}");
            if final_pat == ex {
                return true;
            }
            false
        }
        (_, ExprKind::Normal(p)) => {
            let (ph, pes) = (p.head(), p.elements());
            if BLANK_SYMS.contains(&ph) {
                if is_blank_match(ex.clone(), pat.clone()) {
                    pos_map.insert(pos.to_vec(), ex.clone());
                    return true;
                } else {
                    return false;
                }
            } else if ph == &*PATTERN {
                let b = pes[1].clone();
                if is_blank_match(ex.clone(), b) {
                    if let Some(from_map) = named_map.get(&pat) {
                        return from_map == &ex;
                    } else {
                        // doing both idk why
                        named_map.insert(pat.clone(), ex.clone());
                        pos_map.insert(pos.to_vec(), ex.clone());
                        return true;
                    }
                } else {
                    return false;
                }
            }
            false
        }
        (e, p) => e == p,
    }
}

pub fn run_file(ctx: &mut Context2, filepath: &Path) -> Result<Expr> {
    let file_contents = std::fs::read_to_string(filepath)?;
    println!("Running file: {}", filepath.display());
    // i dont love this because it's ambigious whether or not something failed in reading the file or sth
    // or if the last expr in the file was a setd or something that returns a Null
    let mut res = Expr::null();
    let exprs = expr_parser::expressions(&file_contents).unwrap();
    // for line in reader.lines() {
    for expr in exprs {
        res = evaluate(ctx, expr);
    }

    Ok(res)
}

fn main() -> Result<()> {
    let mut ctx = Context2 {
        vars: HashMap::new(),
    };

    let rl = setup_repl();
    run_file(&mut ctx, Path::new("./lang/attrs.sexp")).unwrap();
    run(rl, &mut ctx).unwrap();

    Ok(())
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
            ("(MatchQ (f (a b) (a c) (a d) 0 (a e) (a f)) (f (BlankSequence a) 0 (BlankSequence a)))", parse("True")),
            ("(MatchQ (f x) (BlankNullSequence f))", parse("True")),
            ("(MatchQ (f x) (f x (BlankNullSequence)))", parse("True")),
            ("(MatchQ (f x) (BlankNullSequence))", parse("True")),

            // named 
            ("(MatchQ 1 (Pattern x (Blank)))", parse("True")),
            ("(MatchQ 1 (Pattern x (Blank Integer)))", parse("True")),
            ("(MatchQ (f x) (Pattern x (Blank)))", parse("True")),
            ("(MatchQ (f x) (Pattern x (Blank f)))", parse("True")),

            ("(MatchQ (f x x) (f (Pattern x (Blank)) (Pattern x (Blank))))", parse("True")),
            ("(MatchQ (f x y) (f (Pattern x (Blank)) (Pattern x (Blank))))", parse("False")),
            ("(MatchQ (f (a b) (a c)) (f (Pattern x (BlankSequence a))))", parse("True")),
            ("(MatchQ (f (a b) (a c)) (f (Pattern x (BlankSequence b))))", parse("False")),

            // https://github.com/anandijain/cas3.rs/issues/18
            ("(MatchQ (f a) (f (BlankNullSequence) (BlankSequence)))", parse("True")),
            ("(MatchQ (f a) (f (Pattern x (BlankNullSequence)) (BlankSequence)))", parse("True")),
            ("(MatchQ (f a) (f (Pattern x (BlankNullSequence)) (Pattern y (BlankSequence))))", parse("True")),
            ("(MatchQ (f a b c d e) (f (BlankSequence) c (BlankSequence)))", parse("True")),
            ("(MatchQ (f a b c d e) (f (Pattern x (BlankSequence)) c (BlankSequence)))", parse("True")),
            ("(MatchQ (f a b c d e) (f (Pattern x (BlankSequence)) c (Pattern x (BlankSequence))))", parse("False")),
            ("(MatchQ (f a b 0 c) (f (BlankSequence) 0 (BlankSequence)))", parse("True")),
        ];

        for (i, (c, e)) in cases.iter().enumerate() {
            println!("\n\nSTARTING MATCH CASE {}: {}", i, c);
            assert_eq!(ctx_evalparse(&mut ctx, c), *e)
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
        // let ex2 = splice_sequences(ex.clone());
        // println!("{}", ex);
        // println!("{}", ex2);
        // for (c, e) in cases {
        // assert_eq!(ctx_evalparse(&mut ctx, c), e)
        // }
    }
}
