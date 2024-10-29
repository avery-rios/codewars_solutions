use std::{
    collections::{hash_map, HashMap},
    rc::Rc,
};

mod ast {
    #[derive(Debug, Clone, Copy)]
    pub enum Op {
        Add,
        Sub,
        Mul,
        Div,
        Mod,
    }
    #[derive(Debug)]
    pub enum Expr<'a> {
        Lit(f32),
        Var(&'a str),
        Assign(&'a str, Box<Expr<'a>>),
        Call(&'a str, Vec<Expr<'a>>),
        Arith(Box<Expr<'a>>, Op, Box<Expr<'a>>),
    }

    #[derive(Debug)]
    pub struct Function<'a> {
        pub name: &'a str,
        pub args: Vec<&'a str>,
        pub body: Expr<'a>,
    }

    #[derive(Debug)]
    pub enum Ast<'a> {
        Expr(Expr<'a>),
        Function(Function<'a>),
        Empty,
    }
}

mod parser {
    use crate::ast;

    type PResult<'a, T> = Option<(T, &'a str)>;

    fn ident(input: &str) -> PResult<&str> {
        if !input.starts_with(|c: char| c.is_alphabetic() || c == '_') {
            return None;
        }
        let (ret, rest) = input.split_at(
            input
                .find(|c: char| c != '_' && !c.is_alphanumeric())
                .unwrap_or(input.len()),
        );
        if ret.is_empty() {
            None
        } else {
            Some((ret, rest))
        }
    }
    fn literal(input: &str) -> PResult<f32> {
        let digits0_end = input
            .char_indices()
            .filter_map(|(idx, c)| if !c.is_ascii_digit() { Some(idx) } else { None })
            .next()
            .unwrap_or(input.len());

        let rest = &input[digits0_end..];
        if let Some(rest) = rest.strip_prefix('.') {
            let digits1_end = rest
                .char_indices()
                .filter_map(|(idx, c)| if !c.is_ascii_digit() { Some(idx) } else { None })
                .next()
                .unwrap_or(rest.len());
            let (digits, rest) = input.split_at(digits0_end + digits1_end + 1);
            Some((digits.parse().ok()?, rest))
        } else {
            let (digits, rest) = input.split_at(digits0_end);
            Some((digits.parse().ok()?, rest))
        }
    }

    fn term<'a>(input: &'a str) -> PResult<'a, ast::Expr<'a>> {
        match input.chars().next()? {
            '0'..='9' => {
                let (ret, input) = literal(input)?;
                Some((ast::Expr::Lit(ret), input))
            }
            '(' => {
                let (ret, input) = expr(input.trim_start_matches('(').trim_start())?;
                Some((ret, input.trim_start().strip_prefix(')')?))
            }
            '_' | 'a'..='z' | 'A'..='Z' => {
                let (ret, input) = ident(input)?;
                Some((ast::Expr::Var(ret), input))
            }
            _ => None,
        }
    }
    fn call_term<'a>(input: &'a str) -> PResult<'a, ast::Expr<'a>> {
        match ident(input) {
            Some((fn_name, input)) => {
                let mut input = input.trim_start();
                let mut args = Vec::new();
                while let Some((arg, rest)) = term(input) {
                    args.push(arg);
                    input = rest.trim_start();
                }
                if args.is_empty() {
                    Some((ast::Expr::Var(fn_name), input))
                } else {
                    Some((ast::Expr::Call(fn_name, args), input))
                }
            }
            None => term(input),
        }
    }
    fn mul_term<'a>(input: &'a str) -> PResult<'a, ast::Expr<'a>> {
        let (mut ret, mut input) = call_term(input)?;
        input = input.trim_start();
        while !input.is_empty() {
            let op = match input.chars().next()? {
                '*' => ast::Op::Mul,
                '/' => ast::Op::Div,
                '%' => ast::Op::Mod,
                _ => break,
            };
            let (rhs, rest) = call_term(&input[1..].trim_start())?;
            ret = ast::Expr::Arith(Box::new(ret), op, Box::new(rhs));
            input = rest.trim_start();
        }
        Some((ret, input))
    }
    fn arith_expr<'a>(input: &'a str) -> PResult<'a, ast::Expr<'a>> {
        let (mut ret, mut input) = mul_term(input)?;
        input = input.trim_start();
        while !input.is_empty() {
            let op = match input.chars().next()? {
                '+' => ast::Op::Add,
                '-' => ast::Op::Sub,
                _ => break,
            };
            let (rhs, rest) = mul_term(&input[1..].trim_start())?;
            ret = ast::Expr::Arith(Box::new(ret), op, Box::new(rhs));
            input = rest.trim_start();
        }
        Some((ret, input))
    }
    fn assign<'a>(input: &'a str) -> PResult<'a, ast::Expr<'a>> {
        let (ident, input) = ident(input)?;
        let input = input.trim_start().strip_prefix('=')?.trim_start();
        let (e, input) = expr(input)?;
        Some((ast::Expr::Assign(ident, Box::new(e)), input))
    }
    fn expr<'a>(input: &'a str) -> PResult<'a, ast::Expr<'a>> {
        assign(input).or_else(|| arith_expr(input))
    }

    fn fun_def<'a>(input: &'a str) -> PResult<'a, ast::Function<'a>> {
        let input = input.strip_prefix("fn ")?.trim_start();
        let (name, input) = ident(input)?;
        let (args, input) = {
            let mut input = input.trim_start();
            let mut ret = Vec::new();
            while let Some((arg, rest)) = ident(input) {
                ret.push(arg);
                input = rest.trim_start();
            }
            (ret, input)
        };
        let input = input.trim_start().strip_prefix("=>")?.trim_start();
        let (body, input) = expr(input)?;
        Some((ast::Function { name, args, body }, input))
    }

    pub fn parse<'a>(input: &'a str) -> Option<ast::Ast<'a>> {
        let input = input.trim();
        if input.is_empty() {
            return Some(ast::Ast::Empty);
        }
        if input.starts_with("fn") {
            match fun_def(input) {
                Some((f, "")) => Some(ast::Ast::Function(f)),
                _ => None,
            }
        } else {
            match expr(input) {
                Some((e, "")) => Some(ast::Ast::Expr(e)),
                _ => None,
            }
        }
    }
}

mod instr {
    use std::rc::Rc;

    pub use crate::ast::Op;

    #[derive(Debug, Clone, Copy)]
    pub struct Addr(pub u32);

    #[derive(Debug)]
    pub enum Instr {
        Arith(Op),
        Load(Addr),
        Store(Addr),
        Push(f32),
        Call(Rc<Function>),
    }

    #[derive(Debug)]
    pub struct Function {
        pub arg_count: usize,
        pub var_size: usize,
        pub instr: Vec<Instr>,
    }
}

type FunctionMap = HashMap<String, Rc<instr::Function>>;

trait AddrMap<'a> {
    fn use_var(&self, v: &str) -> Option<instr::Addr>;
    fn assign_var(&mut self, v: &'a str) -> instr::Addr;
}
struct ExprCompiler<'a, VE> {
    env: VE,
    function_map: &'a FunctionMap,
    instr: Vec<instr::Instr>,
}
impl<'a, VE: AddrMap<'a>> ExprCompiler<'a, VE> {
    fn compile(&mut self, expr: &ast::Expr<'a>) -> Result<(), String> {
        match expr {
            ast::Expr::Lit(v) => self.instr.push(instr::Instr::Push(*v)),
            ast::Expr::Var(v) => match self.env.use_var(*v) {
                Some(a) => self.instr.push(instr::Instr::Load(a)),
                None => match self.function_map.get(*v) {
                    Some(fun) if fun.arg_count == 0 => {
                        self.instr.push(instr::Instr::Call(Rc::clone(fun)))
                    }
                    Some(_) => return Err(format!("ERROR: argument count mismatch for '{v}'")),
                    None => return Err(format!("ERROR: Unknown identifier '{v}'")),
                },
            },
            ast::Expr::Assign(v, e) => {
                self.compile(e)?;
                if self.function_map.contains_key(*v) {
                    return Err(format!("ERROR: {v} is already defined as function"));
                }
                self.instr
                    .push(instr::Instr::Store(self.env.assign_var(*v)));
            }
            ast::Expr::Arith(l, op, r) => {
                self.compile(r)?;
                self.compile(l)?;
                self.instr.push(instr::Instr::Arith(*op));
            }
            ast::Expr::Call(f, args) => {
                let mut cnt = 0;
                for e in args.iter().rev() {
                    match e {
                        ast::Expr::Var(ident) => match self.function_map.get(*ident) {
                            Some(fun) if cnt >= fun.arg_count => {
                                self.instr.push(instr::Instr::Call(Rc::clone(fun)));
                                cnt = cnt + 1 - fun.arg_count;
                            }
                            Some(_) => return Err("ERROR: argument count mismatch".into()),
                            None => {
                                self.compile(e)?;
                                cnt += 1;
                            }
                        },
                        _ => {
                            self.compile(e)?;
                            cnt += 1;
                        }
                    }
                }
                match self.function_map.get(*f) {
                    Some(fun) => {
                        if cnt == fun.arg_count {
                            self.instr.push(instr::Instr::Call(Rc::clone(fun)));
                        } else {
                            return Err("ERROR: argument count mismatch".into());
                        }
                    }
                    None => return Err(format!("ERROR: Unknown identifier '{f}'")),
                }
            }
        }
        Ok(())
    }
}

fn compile_function(fun: &ast::Function) -> Result<instr::Function, String> {
    struct LocalVarAddr<'a>(HashMap<&'a str, instr::Addr>);
    impl<'a> AddrMap<'a> for LocalVarAddr<'a> {
        fn use_var(&self, v: &str) -> Option<instr::Addr> {
            self.0.get(v).copied()
        }
        fn assign_var(&mut self, v: &'a str) -> instr::Addr {
            let size = self.0.len();
            match self.0.entry(v) {
                hash_map::Entry::Occupied(o) => o.get().clone(),
                hash_map::Entry::Vacant(v) => {
                    let addr = instr::Addr(size as u32);
                    v.insert(addr);
                    addr
                }
            }
        }
    }
    let mut compiler = ExprCompiler {
        env: LocalVarAddr({
            let mut ret = HashMap::with_capacity(fun.args.len());
            for (idx, a) in fun.args.iter().enumerate() {
                if let Some(_) = ret.insert(*a, instr::Addr(idx as u32)) {
                    return Err("ERROR: duplicate argument name".into());
                }
            }
            ret
        }),
        function_map: &HashMap::new(),
        instr: Vec::new(),
    };
    compiler.compile(&fun.body)?;
    Ok(instr::Function {
        arg_count: fun.args.len(),
        var_size: compiler.env.0.len(),
        instr: compiler.instr,
    })
}

struct GlobalVarAddr(HashMap<String, instr::Addr>);
impl<'a, 'b> AddrMap<'a> for &'b mut GlobalVarAddr {
    fn use_var(&self, v: &str) -> Option<instr::Addr> {
        self.0.get(v).copied()
    }
    fn assign_var(&mut self, v: &'a str) -> instr::Addr {
        match self.0.get(v) {
            Some(a) => *a,
            None => {
                let addr = instr::Addr(self.0.len() as u32);
                self.0.insert(String::from(v), addr);
                addr
            }
        }
    }
}

fn compile_top_expr(
    function_map: &FunctionMap,
    var_map: &mut GlobalVarAddr,
    expr: &ast::Expr,
) -> Result<Vec<instr::Instr>, String> {
    let mut compiler = ExprCompiler {
        env: var_map,
        function_map,
        instr: Vec::new(),
    };
    compiler.compile(expr)?;
    Ok(compiler.instr)
}

fn interpret(var: &mut [f32], stack: &mut Vec<f32>, instr: &[instr::Instr]) {
    for i in instr {
        match i {
            instr::Instr::Arith(op) => {
                let l = stack.pop().unwrap();
                let r = stack.pop().unwrap();
                stack.push(match *op {
                    instr::Op::Add => l + r,
                    instr::Op::Sub => l - r,
                    instr::Op::Mul => l * r,
                    instr::Op::Div => l / r,
                    instr::Op::Mod => l % r,
                })
            }
            instr::Instr::Load(instr::Addr(a)) => stack.push(var[*a as usize]),
            instr::Instr::Store(instr::Addr(a)) => var[*a as usize] = *stack.last().unwrap(),
            instr::Instr::Push(v) => stack.push(*v),
            instr::Instr::Call(fun) => {
                let mut vars = vec![0.0; fun.var_size];
                for a in 0..fun.arg_count {
                    vars[a] = stack.pop().unwrap();
                }
                interpret(&mut vars, stack, &fun.instr);
            }
        }
    }
}

pub struct Interpreter {
    var_addr: GlobalVarAddr,
    global_var: Vec<f32>,
    stack: Vec<f32>,
    functions: FunctionMap,
}

impl Interpreter {
    pub fn new() -> Interpreter {
        Self {
            var_addr: GlobalVarAddr(HashMap::new()),
            global_var: Vec::new(),
            stack: Vec::new(),
            functions: HashMap::new(),
        }
    }

    pub fn input(&mut self, input: &str) -> Result<Option<f32>, String> {
        match parser::parse(input).ok_or_else(|| String::from("parse failure"))? {
            ast::Ast::Function(fun) => {
                if self.var_addr.0.contains_key(fun.name) {
                    return Err(format!("ERROR: '{}' already exists", fun.name));
                }
                self.functions
                    .insert(fun.name.to_string(), Rc::new(compile_function(&fun)?));
                Ok(None)
            }
            ast::Ast::Expr(expr) => {
                let instr = compile_top_expr(&self.functions, &mut self.var_addr, &expr)?;
                self.global_var.resize(self.var_addr.0.len(), 0.0);
                interpret(&mut self.global_var, &mut self.stack, &instr);
                Ok(self.stack.pop())
            }
            ast::Ast::Empty => Ok(None),
        }
    }
}
