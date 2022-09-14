use proc_macro::TokenStream;

use syn::{
    parse::{
        Parse,
        discouraged::Speculative,
    },
    Token,
    Expr,
    Pat,
};

use quote::quote;

#[proc_macro]
pub fn io (toks: TokenStream) -> TokenStream {

	// There are three types of statement, each delimited by a semicolon,
	// except for the last. In addition, `return(x)` is replaced with
	// `::iom::pure(x)`.
	//
	// The statement types are as follows:
	//
	// 1. Unwrapping/backwards-arrow statements
	// 2. Executing/non-binding statements
	// 3. Let bindings
	//
	// The last statement in a block can only be an executing statement.

	inner(toks.into()).into()
}

fn inner (toks: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
	match syn::parse2::<Block>(toks) {
    	Ok (Block (stmts)) => {
        	let mut merged = proc_macro2::TokenStream::new();

			// Right-fold over all the statements
        	for x in stmts.into_iter().rev() {
            	merged = match x {
                	Statement::Binding (_, pat, _, expr, _) =>
                    	quote! {
                        	{
                            	let #pat = #expr;
                            	#merged
                        	}
                    	},
                    Statement::Execute (expr, _) | Statement::Final (expr) if merged.is_empty() =>
                        quote! {
                        	#expr
                    	},
                    Statement::Execute (expr, _) | Statement::Final (expr) =>
                        quote! {
                            #expr.then(#merged)
                        },
                    Statement::Unwrap (pat, _, expr, _) =>
                        quote! {
                            #expr.bind(|#pat| {
                                #merged
                            })
                        },
            	}
        	}

        	merged.into()
    	},
    	Err (err) => err.into_compile_error().into(),
	}

}

struct Block (Vec<Statement>);

impl Parse for Block {
    fn parse (input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut statements = Vec::new();
        
        while !input.is_empty() {
            match input.parse::<Statement>()? {
                Statement::Final (e) if input.is_empty() => {
                    statements.push(Statement::Final (e));
                    return Ok (Block (statements))
                },
                Statement::Final (_) =>
                    return Err (input.error("Unexpected final statement")),
                stmt => statements.push(stmt),
            }
        }

        Err (input.error("AAAAAAA"))
    }
}

enum Statement {
    Unwrap  (Pat, Token![<-], Expr, Token![;]),
    Binding (Token![let], Pat, Token![=], Expr, Token![;]),
    Execute (Expr, Token![;]),
    Final   (Expr),
}

impl Parse for Statement {
    fn parse (input: syn::parse::ParseStream) -> syn::Result<Self> {
		let f = input.fork();
        if input.peek(Token![let]) {

            // Let binding

    		println!("A branch: '{}'", input.fork().to_string());

			let x = input.parse::<Token![let]>()?;
            let p = input.parse::<Pat>()?;
            let y = input.parse::<Token![=]>()?;
            let e = input.parse::<Expr>()?;
            let s = input.parse::<Token![;]>()?;

            Ok (Statement::Binding (x, p, y, e, s))

        } else if let Ok ((x,y)) = f.parse::<Pat>().and_then(|x| {
            f.parse::<Token![<-]>().map(|y| (x,y))
        }) {

            // Unwrapping

    		// Commit to this path
    		input.advance_to(&f);
            let e = input.parse::<Expr>()?;
            let s = input.parse::<Token![;]>()?;

            Ok (Statement::Unwrap (x, y, e, s))

        } else {

            // Executing

            let e = input.parse::<Expr>()?;

            Ok (match input.parse::<Option<Token![;]>>()? {
            	Some (s) => Statement::Execute (e, s),
            	None => Statement::Final (e),
            })

        }
    }
}
