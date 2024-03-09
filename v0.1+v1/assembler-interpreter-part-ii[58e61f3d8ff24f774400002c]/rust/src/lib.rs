use std::{
    cmp::Ordering,
    collections::{hash_map::Entry, HashMap},
    fmt::Write,
    ops::{Index, IndexMut},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CmpOrder {
    Lt,
    Le,
    Eq,
    Ne,
    Ge,
    Gt,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Reg<R>(R);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Addr<L>(L);

#[derive(Debug, Clone, Copy)]
enum MsgVal<'a, R> {
    Text(&'a str),
    Reg(Reg<R>),
}

#[derive(Debug, Clone, Copy)]
enum Value<R> {
    Reg(Reg<R>),
    Imm(i32),
}

#[derive(Debug, Clone)]
enum Instr<'a, R, L> {
    Mov(Reg<R>, Value<R>),
    Add(Reg<R>, Value<R>),
    Sub(Reg<R>, Value<R>),
    Mul(Reg<R>, Value<R>),
    Div(Reg<R>, Value<R>),
    Jmp(Addr<L>),
    CmpR(Reg<R>, Value<R>),
    CmpIR(i32, Reg<R>),
    CmpII(Ordering),
    JmpCond(CmpOrder, Addr<L>),
    Call(Addr<L>),
    Ret,
    Msg(Box<[MsgVal<'a, R>]>), // reduce size
    End,
}

type PreInst<'a> = Instr<'a, &'a str, &'a str>;

#[derive(Debug)]
struct Labeled<'a> {
    labels: Vec<Addr<&'a str>>,
    instr: PreInst<'a>,
}

mod parser {
    use super::*;

    type PResult<'a, T> = Option<(&'a str, T)>;

    fn take_while1(f: impl Fn(char) -> bool, input: &str) -> PResult<'_, &str> {
        let ci = input.char_indices().take_while(|(_, c)| f(*c)).last()?;
        Some((&input[ci.0 + 1..], &input[0..=ci.0]))
    }
    fn space1(input: &str) -> PResult<'_, ()> {
        if input.chars().next()?.is_whitespace() {
            Some((input.trim_start(), ()))
        } else {
            None
        }
    }

    fn label(input: &str) -> PResult<'_, Addr<&str>> {
        take_while1(|c| c != ':' && !c.is_whitespace(), input).map(|(i, v)| (i, Addr(v)))
    }
    fn reg(input: &str) -> PResult<'_, Reg<&str>> {
        take_while1(char::is_alphabetic, input).map(|(i, v)| (i, Reg(v)))
    }

    fn string(i: &str) -> PResult<'_, &str> {
        i.strip_prefix('\'')?.split_once('\'').map(|(r, i)| (i, r))
    }
    fn int(i: &str) -> PResult<'_, i32> {
        let idx = if i.chars().next()? == '-' {
            i.char_indices().skip(1)
        } else {
            i.char_indices().skip(0)
        }
        .take_while(|(_, c)| c.is_numeric())
        .last()?
        .0;
        Some((&i[idx + 1..], i[0..=idx].parse().ok()?))
    }

    fn value(input: &str) -> PResult<'_, Value<&str>> {
        let fst = input.chars().next()?;
        if fst == '-' || fst.is_numeric() {
            int(input).map(|(i, r)| (i, Value::Imm(r)))
        } else {
            reg(input).map(|(i, r)| (i, Value::Reg(r)))
        }
    }

    fn msg_val(input: &str) -> PResult<'_, MsgVal<'_, &str>> {
        if input.chars().next()? == '\'' {
            string(input).map(|(i, s)| (i, MsgVal::Text(s)))
        } else {
            reg(input).map(|(i, r)| (i, MsgVal::Reg(r)))
        }
    }

    fn u_inst<'a, Op>(
        f: impl Fn(Op) -> PreInst<'a>,
        op: impl Fn(&'a str) -> PResult<'a, Op>,
        i: &'a str,
    ) -> PResult<'a, PreInst<'a>> {
        let (i, _) = space1(i)?;
        let (i, op) = op(i)?;
        Some((i, f(op)))
    }

    fn jmp_inst<'a>(
        f: impl Fn(Addr<&'a str>) -> PreInst<'a>,
        i: &'a str,
    ) -> PResult<'a, PreInst<'a>> {
        u_inst(f, label, i)
    }

    fn cond_jmp_inst(v: CmpOrder, i: &str) -> PResult<'_, PreInst> {
        jmp_inst(|l| Instr::JmpCond(v, l), i)
    }

    fn bin_inst<'a, Op1, Op2>(
        f: impl Fn(Op1, Op2) -> PreInst<'a>,
        op1: impl Fn(&'a str) -> PResult<'a, Op1>,
        op2: impl Fn(&'a str) -> PResult<'a, Op2>,
        i: &'a str,
    ) -> PResult<'a, PreInst<'a>> {
        let (i, _) = space1(i)?;
        let (i, op1) = op1(i)?;
        let i = i.strip_prefix(',')?.trim_start();
        let (i, op2) = op2(i.trim_start())?;
        Some((i, f(op1, op2)))
    }

    fn reg_val_inst<'a>(
        f: impl Fn(Reg<&'a str>, Value<&'a str>) -> PreInst<'a>,
        i: &'a str,
    ) -> PResult<'a, PreInst<'a>> {
        bin_inst(f, reg, value, i)
    }

    fn pre_instr<'a>(input: &'a str) -> PResult<'a, PreInst<'a>> {
        let (i, name) = take_while1(char::is_alphabetic, input)?;
        match name {
            "mov" => reg_val_inst(Instr::Mov, i),
            "inc" => u_inst(|r| Instr::Add(r, Value::Imm(1)), reg, i),
            "dec" => u_inst(|r| Instr::Sub(r, Value::Imm(1)), reg, i),
            "add" => reg_val_inst(Instr::Add, i),
            "sub" => reg_val_inst(Instr::Sub, i),
            "mul" => reg_val_inst(Instr::Mul, i),
            "div" => reg_val_inst(Instr::Div, i),
            "jmp" => jmp_inst(Instr::Jmp, i),
            "cmp" => bin_inst(
                |l, r| match l {
                    Value::Reg(rl) => Instr::CmpR(rl, r),
                    Value::Imm(il) => match r {
                        Value::Reg(rr) => Instr::CmpIR(il, rr),
                        Value::Imm(ir) => Instr::CmpII(il.cmp(&ir)),
                    },
                },
                value,
                value,
                i,
            ),
            "jne" => cond_jmp_inst(CmpOrder::Ne, i),
            "je" => cond_jmp_inst(CmpOrder::Eq, i),
            "jge" => cond_jmp_inst(CmpOrder::Ge, i),
            "jg" => cond_jmp_inst(CmpOrder::Gt, i),
            "jle" => cond_jmp_inst(CmpOrder::Le, i),
            "jl" => cond_jmp_inst(CmpOrder::Lt, i),
            "call" => jmp_inst(Instr::Call, i),
            "ret" => Some((i, Instr::Ret)),
            "msg" => {
                let mut ms = Vec::new();
                let mut i = space1(i)?.0;

                {
                    let (t, m0) = msg_val(i)?;
                    i = t.trim_start();
                    ms.push(m0);
                }

                while let Some(i1) = i.strip_prefix(',') {
                    let (t, m) = msg_val(i1.trim_start())?;
                    i = t.trim_start();
                    ms.push(m);
                }
                Some((i, Instr::Msg(ms.into_boxed_slice())))
            }
            "end" => Some((i, Instr::End)),
            _ => None,
        }
    }

    fn space_comment(mut i: &str) -> &str {
        i = i.trim_start();
        while let Some(t) = i.strip_prefix(';') {
            i = t.trim_start_matches(|c| c != '\n').trim_start();
        }
        i
    }

    fn labeled(mut i: &str) -> PResult<'_, Labeled> {
        let mut lab = Vec::new();
        loop {
            match pre_instr(i) {
                Some((i, instr)) => break Some((i, Labeled { labels: lab, instr })),
                None => {
                    let (t, l) = label(i)?;
                    lab.push(l);
                    i = space_comment(t.strip_prefix(':')?);
                }
            }
        }
    }

    pub(super) fn program(mut input: &str) -> PResult<'_, Vec<Labeled>> {
        let mut ret = Vec::new();
        input = space_comment(input);
        while !input.is_empty() {
            let (t, l) = labeled(input)?;
            ret.push(l);
            input = space_comment(t);
        }
        Some((input, ret))
    }
}

type AddrMap<'a> = HashMap<Addr<&'a str>, Addr<u16>>;
type RegMap<'a> = HashMap<Reg<&'a str>, Reg<u16>>;

fn addr_map<'a>(instr: &[Labeled<'a>]) -> Option<AddrMap<'a>> {
    let mut ret = HashMap::new();
    for (idx, ls) in instr.iter().enumerate() {
        let addr = Addr(idx as u16);
        for l in ls.labels.iter().copied() {
            if let Some(_) = ret.insert(l, addr) {
                return None;
            }
        }
    }
    Some(ret)
}

type NInstr<'a> = Instr<'a, u16, u16>;

struct Convertor<'a> {
    reg_map: RegMap<'a>,
}
impl<'a> Convertor<'a> {
    fn reg(&mut self, reg: Reg<&'a str>) -> Reg<u16> {
        let l = self.reg_map.len() as u16;
        match self.reg_map.entry(reg) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(v) => {
                let r = Reg(l);
                v.insert(r);
                r
            }
        }
    }
    fn value(&mut self, value: Value<&'a str>) -> Value<u16> {
        match value {
            Value::Imm(i) => Value::Imm(i),
            Value::Reg(r) => Value::Reg(self.reg(r)),
        }
    }

    fn convert<'b>(pre_instr: Vec<Labeled<'b>>) -> Option<(usize, Vec<NInstr<'b>>)> {
        let am = addr_map(&pre_instr)?;
        let mut conv = Self {
            reg_map: RegMap::new(),
        };
        let mut ret = Vec::with_capacity(pre_instr.len());
        for i in pre_instr.into_iter() {
            ret.push(match i.instr {
                Instr::Mov(r, v) => Instr::Mov(conv.reg(r), conv.value(v)),
                Instr::Add(r, v) => Instr::Add(conv.reg(r), conv.value(v)),
                Instr::Sub(r, v) => Instr::Sub(conv.reg(r), conv.value(v)),
                Instr::Mul(r, v) => Instr::Mul(conv.reg(r), conv.value(v)),
                Instr::Div(r, v) => Instr::Div(conv.reg(r), conv.value(v)),
                Instr::Jmp(a) => Instr::Jmp(*am.get(&a)?),
                Instr::CmpR(r, v) => Instr::CmpR(conv.reg(r), conv.value(v)),
                Instr::CmpIR(i, r) => Instr::CmpIR(i, conv.reg(r)),
                Instr::CmpII(v) => Instr::CmpII(v),
                Instr::JmpCond(c, a) => Instr::JmpCond(c, *am.get(&a)?),
                Instr::Call(a) => Instr::Call(*am.get(&a)?),
                Instr::Ret => Instr::Ret,
                Instr::Msg(ms) => Instr::Msg({
                    let mut ret = Vec::with_capacity(ms.len());
                    for m in ms.into_iter() {
                        ret.push(match m {
                            MsgVal::Reg(r) => MsgVal::Reg(conv.reg(*r)),
                            MsgVal::Text(t) => MsgVal::Text(t),
                        });
                    }
                    ret.into_boxed_slice()
                }),
                Instr::End => Instr::End,
            })
        }
        Some((conv.reg_map.len(), ret))
    }
}

struct RegField(Vec<i32>);
impl RegField {
    #[inline]
    fn value(&self, value: Value<u16>) -> i32 {
        match value {
            Value::Imm(i) => i,
            Value::Reg(r) => self[r],
        }
    }
}
impl Index<Reg<u16>> for RegField {
    type Output = i32;
    #[inline]
    fn index(&self, index: Reg<u16>) -> &Self::Output {
        unsafe { self.0.get_unchecked(index.0 as usize) }
    }
}
impl IndexMut<Reg<u16>> for RegField {
    #[inline]
    fn index_mut(&mut self, index: Reg<u16>) -> &mut Self::Output {
        unsafe { self.0.get_unchecked_mut(index.0 as usize) }
    }
}

fn interp(reg_cnt: usize, instr: &[NInstr<'_>]) -> Option<String> {
    let mut output = String::new();
    let mut stack = Vec::new();
    let mut regs = {
        let mut v = Vec::with_capacity(reg_cnt);
        v.resize(reg_cnt, 0);
        RegField(v)
    };
    let mut cmp_state = Ordering::Equal;
    let mut pc = 0;
    while let Some(i) = instr.get(pc) {
        match i {
            Instr::Mov(r1, v) => {
                regs[*r1] = regs.value(*v);
                pc += 1;
            }
            Instr::Add(r1, v) => {
                regs[*r1] += regs.value(*v);
                pc += 1
            }
            Instr::Sub(r1, v) => {
                regs[*r1] -= regs.value(*v);
                pc += 1;
            }
            Instr::Mul(r1, v) => {
                regs[*r1] *= regs.value(*v);
                pc += 1;
            }
            Instr::Div(r1, v) => {
                regs[*r1] /= regs.value(*v);
                pc += 1;
            }
            Instr::Jmp(i) => {
                pc = i.0 as usize;
            }
            Instr::CmpR(r1, v) => {
                cmp_state = regs[*r1].cmp(&regs.value(*v));
                pc += 1;
            }
            Instr::CmpIR(i, r2) => {
                cmp_state = i.cmp(&regs[*r2]);
                pc += 1;
            }
            Instr::CmpII(s) => {
                cmp_state = *s;
                pc += 1;
            }
            Instr::JmpCond(c, a) => {
                let cond = match *c {
                    CmpOrder::Lt => cmp_state.is_lt(),
                    CmpOrder::Le => cmp_state.is_le(),
                    CmpOrder::Eq => cmp_state.is_eq(),
                    CmpOrder::Ne => cmp_state.is_ne(),
                    CmpOrder::Ge => cmp_state.is_ge(),
                    CmpOrder::Gt => cmp_state.is_gt(),
                };
                pc = if cond { a.0 as usize } else { pc + 1 };
            }
            Instr::Call(a) => {
                stack.push(pc + 1);
                pc = a.0 as usize;
            }
            Instr::Ret => {
                pc = stack.pop()?;
            }
            Instr::Msg(m) => {
                for i in m.into_iter() {
                    match *i {
                        MsgVal::Reg(r) => {
                            write!(&mut output, "{}", regs[r]).ok()?;
                        }
                        MsgVal::Text(t) => output.push_str(t),
                    }
                }
                pc += 1;
            }
            Instr::End => return Some(output),
        }
    }
    None
}

pub struct AssemblerInterpreter;

impl AssemblerInterpreter {
    pub fn interpret(input: &str) -> Option<String> {
        let pis = parser::program(input)?.1;
        let (reg_cnt, inst) = Convertor::convert(pis)?;
        interp(reg_cnt, &inst)
    }
}
