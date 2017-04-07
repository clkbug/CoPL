// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat
open System

type BinOP = 
  | Plus
  | Minus
  | Times
  | LessThan

type Name = string

type Exp = 
  | Var of Name
  | Int of int
  | Bool of bool
  | Op of BinOP * Exp * Exp
  | If of Exp * Exp * Exp
  | MetaOp of BinOP * Exp * Exp
  | Let of Name * Exp * Exp
  | Fun of Name * Exp
  | LetRec of Name * Name * Exp * Exp
  | Closure of Env * Name * Exp
  | RecClosure of Env * Name * Name * Exp
  | Apply of Exp * Exp

and Env = (string * Exp) list

type Judgment = Env * Exp * Exp

type Conclusion = Judgment

type Derivation = 
  | EInt of Conclusion
  | EBool of Conclusion
  | EIfT of Derivation * Derivation * Conclusion
  | EIfF of Derivation * Derivation * Conclusion
  | EPlus of Derivation * Derivation * Derivation * Conclusion
  | EMinus of Derivation * Derivation * Derivation * Conclusion
  | ETimes of Derivation * Derivation * Derivation * Conclusion
  | ELt of Derivation * Derivation * Derivation * Conclusion
  | BPlus of Conclusion
  | BMinus of Conclusion
  | BTimes of Conclusion
  | BLt of Conclusion
  | ELet of Derivation * Derivation * Conclusion
  | EVar1 of Conclusion
  | EVar2 of Derivation * Conclusion
  | EFun of Conclusion
  | EApp of Derivation * Derivation * Derivation * Conclusion
  | ELetRec of Derivation * Conclusion
  | EAppRec of Derivation * Derivation * Derivation * Conclusion

let c2op c = 
  match c with
  | '+' -> Plus
  | '-' -> Minus
  | '*' -> Times
  | '<' -> LessThan
  | _ -> failwith "can't reach here"

let op2s op = 
  match op with
  | Plus -> "+"
  | Minus -> "-"
  | Times -> "*"
  | LessThan -> "<"

let op2ws op = 
  match op with
  | Plus -> "plus"
  | Minus -> "minus"
  | Times -> "times"
  | LessThan -> "less than"

let rec expToString e = 
  match e with
  | Int(n) -> string n
  | Bool(b) -> 
    if b then "true"
    else "false"
  | Var(n) -> n
  | Op(op, e1, e2) -> sprintf "(%s %s %s)" (expToString e1) (op2s op) (expToString e2)
  | If(e1, e2, e3) -> sprintf "(if %s then %s else %s)" (expToString e1) (expToString e2) (expToString e3)
  | MetaOp(op, e1, e2) -> sprintf "%s %s %s" (expToString e1) (op2ws op) (expToString e2)
  | Let(n, e1, e2) -> sprintf "(let %s = %s in %s)" n (expToString e1) (expToString e2)
  | Fun(n, e) -> sprintf "(fun %s -> %s)" n (expToString e)
  | LetRec(n1, n2, e1, e2) -> sprintf "(let rec %s = fun %s -> %s in %s)" n1 n2 (expToString e1) (expToString e2)
  | Closure(env, n, exp) -> sprintf "(%s)[fun %s -> %s]" (envToString env) n (expToString exp)
  | Apply(e1, e2) -> sprintf "(%s %s)" (expToString e1) (expToString e2)
  | RecClosure(env, n1, n2, exp) -> sprintf "(%s)[rec %s = fun %s -> %s]" (envToString env) n1 n2 (expToString exp)

and envToString env = 
  let elemToString (name, v) = sprintf "%s = %s" name (expToString v)
  List.map elemToString env
  |> List.rev
  |> String.concat ", "
  |> fun x -> 
    if x = "" then ""
    else x + " "

let rec derivationToString d = 
  let indent (s : string) = "\t" + s.Replace("\n", "\n\t")
  let indDTS = derivationToString >> indent
  match d with
  | EInt(env, Int(i), _) -> sprintf "%s|- %d evalto %d by E-Int{};" (envToString env) i i
  | EBool(env, b, _) -> sprintf "%s|- %s evalto %s by E-Bool{};" (envToString env) (expToString b) (expToString b)
  | EVar1(env, n, v) -> sprintf "%s|- %s evalto %s by E-Var1{};" (envToString env) (expToString n) (expToString v)
  | EVar2(d, (env, n, v)) -> 
    sprintf "%s|- %s evalto %s by E-Var2{\n%s\n};" (envToString env) (expToString n) (expToString v) (indDTS d)
  | EIfT(d1, d2, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-IfT{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2)
  | EIfF(d1, d2, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-IfF{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2)
  | EPlus(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-Plus{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | EMinus(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-Minus{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | ETimes(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-Times{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | ELt(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-Lt{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2) (indDTS d3)
  | ELet(d1, d2, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-Let{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2)
  | ELetRec(d, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-LetRec{\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d)
  | BPlus(_, exp, v) -> sprintf "%s is %s by B-Plus{};" (expToString exp) (expToString v)
  | BMinus(_, exp, v) -> sprintf "%s is %s by B-Minus{};" (expToString exp) (expToString v)
  | BTimes(_, exp, v) -> sprintf "%s is %s by B-Times{};" (expToString exp) (expToString v)
  | BLt(_, exp, v) -> sprintf "%s is %s by B-Lt{};" (expToString exp) (expToString v)
  | EFun(env, exp, v) -> sprintf "%s|- %s evalto %s by E-Fun{};" (envToString env) (expToString exp) (expToString v)
  | EApp(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-App{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | EAppRec(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-AppRec{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | _ -> failwithf "can't reach here...\n%A" d

let rec eval env exp = 
  match exp with
  | Int(_) -> EInt(env, exp, exp), exp
  | Bool(_) -> EBool(env, exp, exp), exp
  | Var(name) -> 
    match env with
    | (x, v) :: xs -> 
      if x = name then EVar1(env, exp, v), v
      else 
        let (d, v') = eval xs exp
        EVar2(d, (env, exp, v')), v'
    | _ -> failwith "can't reach here."
  | If(e1, e2, e3) -> 
    let (d1, v1) = eval env e1
    if v1 = Bool(true) then 
      let (d2, v2) = eval env e2
      EIfT(d1, d2, (env, exp, v2)), v2
    else 
      let (d3, v3) = eval env e3
      EIfF(d1, d3, (env, exp, v3)), v3
  | Op(op, e1, e2) -> 
    let (d1, v1) = eval env e1
    let (d2, v2) = eval env e2
    let (d3, v3) = eval env (MetaOp(op, v1, v2))
    
    let d = 
      match op with
      | Plus -> EPlus
      | Minus -> EMinus
      | Times -> ETimes
      | LessThan -> ELt
    d (d1, d2, d3, (env, exp, v3)), v3
  | MetaOp(Plus, Int(n1), Int(n2)) -> BPlus((env, exp, Int(n1 + n2))), Int(n1 + n2)
  | MetaOp(Minus, Int(n1), Int(n2)) -> BMinus((env, exp, Int(n1 - n2))), Int(n1 - n2)
  | MetaOp(Times, Int(n1), Int(n2)) -> BTimes((env, exp, Int(n1 * n2))), Int(n1 * n2)
  | MetaOp(LessThan, Int(n1), Int(n2)) -> BLt((env, exp, Bool(n1 < n2))), Bool(n1 < n2)
  | Let(name, e1, e2) -> 
    let (d1, v1) = eval env e1
    let (d2, v2) = eval ((name, v1) :: env) e2
    ELet(d1, d2, (env, exp, v2)), v2
  | Fun(name, e) -> EFun(env, exp, Closure(env, name, e)), Closure(env, name, e)
  | LetRec(n1, n2, e1, e2) -> 
    let d, v = eval ((n1, RecClosure(env, n1, n2, e1)) :: env) e2
    ELetRec(d, (env, exp, v)), v
  | Apply(e1, e2) -> 
    let (d1, v1) = eval env e1
    let (d2, v2) = eval env e2
    match v1 with
    | Closure(env', name, e0) -> 
      let (d3, v) = eval ((name, v2) :: env') e0
      EApp(d1, d2, d3, (env, exp, v)), v
    | RecClosure(env', n1, n2, e0) -> 
      let d3, v = eval ((n2, v2) :: (n1, v1) :: env') e0
      EAppRec(d1, d2, d3, (env, exp, v)), v
    | _ -> failwithf "can't reach here..."
  | _ -> failwithf "can't reach here... in eval %A\n" exp

[<EntryPoint>]
let main argv = 
  //  let f s = 
  //    parseJudgment s
  //    |> (fun (x, y, _) -> eval x y)
  //    |> fst
  //    |> derivationToString
  //    |> printfn "\n%s\n"
  //  
  //  let propositions = 
  //    [ //"|- fun x -> (x + 1) evalto ()[fun x -> x + 1]"; 
  //    "|- let y = 2 in fun x -> x + y evalto (y=2)[fun x -> x + y]"; 
  //      "|- let sq = fun x -> x * x in sq 3 + sq 4 evalto 25"; 
  //      "|- let sm = fun f -> f 3 + f 4 in sm (fun x -> x * x) evalto 25"; 
  //      "|- let max = fun x -> fun y -> if x < y then y else x in max 3 5 evalto 5"; 
  //      "|- let a = 3 in let f = fun y -> y * a in let a = 5 in f 4 evalto 12"; 
  //      "|- let twice = fun f -> fun x -> f (f x) in twice (fun x -> x * x) 2 evalto 16"; 
  //      "|- let twice = fun f -> fun x -> f (f x) in twice twice (fun x -> x * x) 2 evalto 65536"; 
  //  List.map f propositions |> ignore
  let p = 
    [ Fun("x", Op(Plus, Var("x"), Int(1)))
      Let("y", Int(2), Fun("x", Op(Plus, Var("x"), Var("y"))))
      Let("sq", Fun("x", Op(Times, Var("x"), Var("x"))), Op(Plus, Apply(Var("sq"), Int(3)), Apply(Var("sq"), Int(4))))
      
      Let
        ("sm", Fun("f", Op(Plus, Apply(Var("f"), Int(3)), Apply(Var("f"), Int(4)))), 
         Apply(Var("sm"), Fun("x", Op(Times, Var("x"), Var("x")))))
      
      Let
        ("max", Fun("x", Fun("y", If(Op(LessThan, Var("x"), Var("y")), Var("y"), Var("x")))), 
         Apply(Apply(Var("max"), Int(3)), Int(5)))
      Let("a", Int(3), Let("f", Fun("y", Op(Times, Var("y"), Var("a"))), Let("a", Int(5), Apply(Var("f"), Int(4)))))
      
      Let
        ("twice", Fun("f", Fun("x", Apply(Var("f"), Apply(Var("f"), Var("x"))))), 
         Apply(Apply(Var("twice"), Fun("x", Op(Times, Var("x"), Var("x")))), Int(2)))
      
      Let
        ("twice", Fun("f", Fun("x", Apply(Var("f"), Apply(Var("f"), Var("x"))))), 
         Apply(Apply(Apply(Var("twice"), Var("twice")), Fun("x", Op(Times, Var("x"), Var("x")))), Int(2)))
      
      //      "|- let compose = fun f -> fun g -> fun x -> f (g x) in    let p = fun x -> x * x in   let q = fun x -> x + 4 in   compose p q 4   evalto 64"; 
      Let
        ("compose", Fun("f", Fun("g", Fun("x", Apply(Var("f"), Apply(Var("g"), Var("x")))))), 
         Let
           ("p", Fun("x", Op(Times, Var("x"), Var("x"))), 
            Let
              ("q", Fun("x", Op(Plus, Var("x"), Int(4))), 
               Apply(Apply(Apply(Var("compose"), Var("p")), Var("q")), Int(4)))))
      
      //      "|- let s = fun f -> fun g -> fun x -> f x (g x) in   let k = fun x -> fun y -> x in   s k k 7  evalto 7"; 
      Let
        ("s", Fun("f", Fun("g", Fun("x", Apply(Apply(Var("f"), Var("x")), Apply(Var("g"), Var("x")))))), 
         Let("k", Fun("x", Fun("y", Var("x"))), Apply(Apply(Apply(Var("s"), Var("k")), Var("k")), Int(7))))
      
      //      "|- let rec fact = fun n ->   if n < 2 then 1 else n * fact (n - 1) in   fact 3  evalto 6"; 
      LetRec
        ("fact", "n", 
         If
           (Op(LessThan, Var("n"), Int(2)), Int(1), Op(Times, Var("n"), Apply(Var("fact"), Op(Minus, Var("n"), Int(1))))), 
         Apply(Var("fact"), Int(3)))
      
      //      "|- let rec fib = fun n -> if n < 3 then 1 else fib (n - 1) + fib (n - 2) in   fib 5  evalto 5"; 
      LetRec
        ("fib", "n", 
         If
           (Op(LessThan, Var("n"), Int(3)), Int(1), 
            Op(Plus, Apply(Var("fib"), Op(Minus, Var("n"), Int(1))), Apply(Var("fib"), Op(Minus, Var("n"), Int(2))))), 
         Apply(Var("fib"), Int(5)))
      
      //      "|- let rec sum = fun f -> fun n ->     if n < 1 then 0 else f n + sum f (n - 1) in    sum (fun x -> x * x) 2  evalto 5"; 
      LetRec
        ("sum", "f", 
         Fun
           ("n", 
            If
              (Op(LessThan, Var("n"), Int(1)), Int(0), 
               Op(Plus, Apply(Var("f"), Var("n")), Apply(Apply(Var("sum"), Var("f")), Op(Minus, Var("n"), Int(1)))))), 
         Apply(Apply(Var("sum"), Fun("x", Op(Times, Var("x"), Var("x")))), Int(2)))
      
      //      "|- let fact = fun self -> fun n ->     if n < 2 then 1 else n * self self (n - 1) in   fact fact 3  evalto 6" ]
      Let
        ("fact", 
         Fun
           ("self", 
            Fun
              ("n", 
               If
                 (Op(LessThan, Var("n"), Int(2)), Int(1), 
                  Op(Times, Var("n"), Apply(Apply(Var("self"), Var("self")), Op(Minus, Var("n"), Int(1))))))), 
         Apply(Apply(Var("fact"), Var("fact")), Int(3))) ]
  
  let g p = 
    eval [] p
    |> fst
    |> derivationToString
    |> fun x -> x.Replace("\t", "  ")
    |> printfn "\n%s\n"
  
  List.map g p |> ignore
  0 // 整数の終了コードを返します

