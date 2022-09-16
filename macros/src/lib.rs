use proc_macro::TokenStream;

use syn::{
    parse_quote,
    parse::{
        discouraged::Speculative,
        Parse,
    },
    punctuated::{
        Pair,
        Punctuated,
    },
    Token,
    Expr,
    Pat,
    ExprReturn,
    Stmt,
};
use quote::{
    quote,
    ToTokens,
};

#[proc_macro]
pub fn io (toks: TokenStream) -> TokenStream {
    inner(toks.into()).into()
}

fn inner (toks: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    let block = syn::parse2(toks).and_then(preproc);

    match block {
        Ok (Block (mut stmts)) => {
            let init = match stmts.pop() {
                Some (Term::Final { expr }) => expr.to_token_stream(),
                _ => panic!("Bad AST"),
            };
            
            stmts.into_iter().rfold(init, |acc, x| match x {
                Term::Binding { patt, expr } =>
                    quote! {
                        {
                            let #patt = #expr;
                            #acc
                        }
                    },
                Term::Statement { expr } =>
                    quote! {
                        #expr.then(#acc)
                    },
                Term::Unwrap { patt, expr } =>
                    quote! {
                        #expr.bind(|#patt| {
                            #acc
                        })
                    },
                _ => panic!("Bad AST"),
            }).into()
        },
        Err (err) => err.into_compile_error().into(),
    }

}


/// A do-block.
struct Block (Vec<Term>);

/// Do preprocessing on each [`Term`] in the block
fn preproc (Block (data): Block) -> syn::Result<Block> {
    data.into_iter()
        .map(return_to_pure)
        .collect::<syn::Result<Vec<Term>>>()
        .map(Block)
}

/// Transforms `return x` to `pure(x)`.
fn return_to_pure (term: Term) -> syn::Result<Term> {
    fn walk (expr: Expr) -> syn::Result<Expr> {

        // Walks each sub-expression in a block.
        let walk_block = |expr| {
            let syn::Block { brace_token, stmts } = expr;
            stmts.into_iter()
                .map(|s| match s {
                    Stmt::Expr (expr) => {
                        Ok (Stmt::Expr (walk(expr)?))
                    },
                    Stmt::Semi (expr, s) => {
                        Ok (Stmt::Semi (walk(expr)?, s))
                    },
                    s => Ok (s),
                })
                .collect::<syn::Result<Vec<Stmt>>>()
                .map(|stmts| syn::Block { brace_token, stmts })
        };

        // Walks each sub-expression in a punctuated list.
        let walk_list = |args: Punctuated<_, _>| {
            args.into_pairs()
                .map(|pair| match pair {
                    Pair::Punctuated (e, p) => walk(e).map(|e| Pair::Punctuated(e, p)),
                    Pair::End (e) => walk(e).map(Pair::End),
                })
                .collect::<syn::Result<_>>()
        };
        
        match expr {

            // If it's a return expression, we mess with it to turn it into a call to `pure`
            // instead.
            Expr::Return (ExprReturn { expr, .. }) => {
                match expr {
                    Some (expr) => Ok (parse_quote! {
                        ::iom::pure(#expr)
                    }),
                    None => Err (
                        syn::Error::new_spanned(expr, "Missing a value to return")
                    )
                }
            },

            // Expressions that have a subexpression that can reasonably be expected
            // to be of type `IO` are traversed. If those contain a return expression,
            // that expression is transformed, otherwise nothing happens.

            Expr::If (mut expr) => {
                expr.then_branch = walk_block(expr.then_branch)?;
                expr.else_branch = match expr.else_branch {
                    Some ((e, expr)) => Some ((e, walk(*expr).map(Box::new)?)),
                    None => None,
                };
                Ok (Expr::If (expr))
            },
            Expr::Match (mut expr) => {
                expr.arms = expr.arms
                    .into_iter()
                    .map(|mut arm| {
                        arm.body = walk(*arm.body).map(Box::new)?;
                        Ok (arm)
                    })
                    .collect::<syn::Result<_>>()?;
                Ok (Expr::Match (expr))
            },
            Expr::While (mut expr) => {
                expr.body = walk_block(expr.body)?;
                Ok (Expr::While (expr))
            },
            Expr::ForLoop (mut expr) => {
                expr.body = walk_block(expr.body)?;
                Ok (Expr::ForLoop (expr))
            },
            Expr::Loop (mut expr) => {
                expr.body = walk_block(expr.body)?;
                Ok (Expr::Loop (expr))
            },
            Expr::Break (mut expr) => {
                expr.expr = expr.expr
                    .map(|e| walk(*e).map(Box::new))
                    .transpose()?;
                Ok (Expr::Break (expr))
            },
            Expr::Block (mut expr) => {
                expr.block = walk_block(expr.block)?;
                Ok (Expr::Block (expr))
            },
            Expr::TryBlock (mut expr) => {
                expr.block = walk_block(expr.block)?;
                Ok (Expr::TryBlock (expr))
            },
            Expr::Unsafe (mut expr) => {
                expr.block = walk_block(expr.block)?;
                Ok (Expr::Unsafe (expr))
            },
            Expr::Yield (mut expr) => {
                expr.expr = expr.expr
                    .map(|e| walk(*e).map(Box::new))
                    .transpose()?;
                Ok (Expr::Yield (expr))
            },
            Expr::Group (mut expr) => {
                expr.expr = walk(*expr.expr).map(Box::new)?;
                Ok (Expr::Group (expr))
            },
            Expr::Paren (mut expr) => {
                expr.expr = walk(*expr.expr).map(Box::new)?;
                Ok (Expr::Paren (expr))
            },
            Expr::Call (mut expr) => {
                expr.args = walk_list(expr.args)?;
                Ok (Expr::Call (expr))
            },
            Expr::MethodCall (mut expr) => {
                expr.receiver = walk(*expr.receiver).map(Box::new)?;
                expr.args = walk_list(expr.args)?;
                Ok (Expr::MethodCall (expr))
            },
            Expr::Tuple (mut expr) => {
                expr.elems = walk_list(expr.elems)?;
                Ok (Expr::Tuple (expr))
            },
            Expr::Struct (mut expr) => {
                expr.fields = expr.fields
                    .into_pairs()
                    .map(|pair| match pair {
                        Pair::Punctuated (mut e, p) => {
                            e.expr = walk(e.expr)?;
                            Ok (Pair::Punctuated(e, p))
                        },
                        Pair::End (mut e) => {
                            e.expr = walk(e.expr)?;
                            Ok (Pair::End(e))
                        },
                    })
                    .collect::<syn::Result<_>>()?;
                Ok (Expr::Struct (expr))
            },

            // All other expressions are returned unchanged.
            expr => return Ok (expr),

        }
    }
    
    match term {
        Term::Unwrap { patt, mut expr } => {
            expr = walk(expr)?;
            Ok (Term::Unwrap { patt, expr })
        },
        Term::Binding { patt, mut expr } => {
            expr = walk(expr)?;
            Ok (Term::Binding { patt, expr })
        },
        Term::Statement { mut expr } => {
            // This doesn't make much sense but eh
            expr = walk(expr)?;
            Ok (Term::Statement { expr })
        },
        Term::Final { mut expr } => {
            expr = walk(expr)?;
            Ok (Term::Final { expr })
        },
    }
}

impl Parse for Block {
    fn parse (input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut statements = Vec::new();
        
        while !input.is_empty() {
            match input.parse::<Term>()? {
                Term::Final { expr } if input.is_empty() => {
                    statements.push(Term::Final { expr });
                    return Ok (Block (statements))
                },
                Term::Final { .. } =>
                    return Err (input.error("Unexpected final statement")),
                stmt => statements.push(stmt),
            }
        }

        Err (match statements.last() {
            Some (_) => input.error("Do block must terminate with an expression"),
            None => input.error("Do blocks can not be empty"),
        })
    }
}

/// Represents a single action in a [`Block`].
enum Term {
    /// `<patt> <- <expr> ;`
    Unwrap { patt: Pat, expr: Expr },
    /// `let <patt> = <expr> ;`
    Binding { patt: Pat, expr: Expr },
    /// `do <expr> ;`
    Statement { expr: Expr },
    /// `<expr>`, only allowed as the last "statement"
    Final { expr: Expr },
}

impl Parse for Term {
    fn parse (input: syn::parse::ParseStream) -> syn::Result<Self> {

        if input.peek(Token![let]) {

            // Let binding

            input.parse::<Token![let]>()?;
            let patt = input.parse()?;
            input.parse::<Token![=]>()?;
            let expr = input.parse()?;
            input.parse::<Token![;]>()?;

            Ok (Term::Binding { patt, expr })

        } else if input.peek(Token![do]) {

            // Executing "do-statement"

            input.parse::<Token![do]>()?;
            let expr = input.parse()?;
            input.parse::<Token![;]>()?;

            Ok (Term::Statement { expr })

        } else {

            // Speculative attempt to parse an unwrapping binding term.
            // If it fails to parse, the original token stream is left
            // as it is.
            let fork = input.fork();
            if let Ok (patt) = fork.parse().and_then(|patt| fork.parse::<Token![<-]>().map(|_| patt)) {

                // Unwrapping expression

                let expr = fork.parse()?;
                fork.parse::<Token![;]>()?;

                // Sync the fork to the input
                input.advance_to(&fork);

                return Ok (Term::Unwrap { patt, expr })

            }

            // Final expression (no semicolon)
            input.parse().map(|expr| Term::Final { expr })

        }

    }
}
