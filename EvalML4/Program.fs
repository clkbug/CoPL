// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
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
  | Empty
  | Cons of Exp * Exp
  | Match of Exp * Exp * Name * Name * Exp

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
  | EVar of Conclusion
  | EFun of Conclusion
  | EApp of Derivation * Derivation * Derivation * Conclusion
  | ELetRec of Derivation * Conclusion
  | EAppRec of Derivation * Derivation * Derivation * Conclusion
  | ENil of Conclusion
  | ECons of Derivation * Derivation * Conclusion
  | EMatchNil of Derivation * Derivation * Conclusion
  | EMatchCons of Derivation * Derivation * Conclusion

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
  | Empty -> "[]"
  | Cons(x, xs) -> sprintf "(%s :: %s)" (expToString x) (expToString xs)
  | Match(e1, e2, n1, n2, e3) -> 
    sprintf "(match %s with [] -> %s | %s :: %s -> %s)" (expToString e1) (expToString e2) n1 n2 (expToString e3)

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
  | EVar(env, n, v) -> sprintf "%s|- %s evalto %s by E-Var{};" (envToString env) (expToString n) (expToString v)
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
  | ENil(env, exp, v) -> sprintf "%s|- %s evalto %s by E-Nil{};" (envToString env) (expToString exp) (expToString v)
  | ECons(d1, d2, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-Cons{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2)
  | EMatchNil(d1, d2, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-MatchNil{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2)
  | EMatchCons(d1, d2, (env, exp, v)) -> 
    sprintf "%s|- %s evalto %s by E-MatchCons{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2)
  | _ -> failwithf "can't reach here...\n%A" d

let rec eval env exp = 
  match exp with
  | Int(_) -> EInt(env, exp, exp), exp
  | Bool(_) -> EBool(env, exp, exp), exp
  | Var(name) -> 
    let v = List.find (fun x -> fst x = name) env |> snd
    EVar(env, exp, v), v
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
  | Empty -> ENil(env, exp, Empty), Empty
  | Cons(e1, e2) -> 
    let d1, v1 = eval env e1
    let d2, v2 = eval env e2
    ECons(d1, d2, (env, exp, Cons(v1, v2))), Cons(v1, v2)
  | Match(e1, e2, n1, n2, e3) -> 
    let d1, v1 = eval env e1
    match v1 with
    | Empty -> 
      let d2, v2 = eval env e2
      EMatchNil(d1, d2, (env, exp, v2)), v2
    | Cons(v1, v2) -> 
      let d2, v3 = eval ((n2, v2) :: (n1, v1) :: env) e3
      EMatchCons(d1, d2, (env, exp, v3)), v3
    | _ -> failwithf "can't reach here... in eval %A\n" exp
  | _ -> failwithf "can't reach here... in eval %A\n" exp

[<EntryPoint>]
let main argv = 
  //   |- (1 + 2) :: (3 + 4) :: [] evalto 3 :: 7 :: []
  //  |- let f = fun x -> match x with [] -> 0 | a :: b -> a in
  //    f (4::[]) + f [] + f (1 :: 2 :: 3 :: [])
  //   evalto 5
  //  |- let rec f = fun x -> if x < 1 then [] else x :: f (x - 1) in    f 3 evalto 3 :: 2 :: 1 :: []
  // |- let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in    length (1 :: 2 :: 3 :: []) evalto 3
  //  |- let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in    length ((1 :: 2 :: []) :: (3 :: 4 :: 5 :: []) :: []) evalto 2
  // |- let rec append = fun l1 -> fun l2 ->       match l1 with [] -> l2 | x :: y -> x :: append y l2 in    append (1 :: 2 :: []) (3 :: 4 :: 5 :: []) evalto 1 :: 2 :: 3 :: 4 :: 5 :: []
  let p = 
    [ Cons(Op(Plus, Int(1), Int(2)), Cons(Op(Plus, Int(3), Int(4)), Empty))
      
      Let
        ("f", Fun("x", Match(Var("x"), Int(0), "a", "b", Var("a"))), 
         Op
           (Plus, Op(Plus, Apply(Var("f"), Cons(Int(4), Empty)), Apply(Var("f"), Empty)), 
            Apply(Var("f"), Cons(Int(1), Cons(Int(2), Cons(Int(3), Empty))))))
      
      LetRec
        ("f", "x", 
         If(Op(LessThan, Var("x"), Int(1)), Empty, Cons(Var("x"), Apply(Var("f"), Op(Minus, Var("x"), Int(1))))), 
         Apply(Var("f"), Int(3)))
      
      LetRec
        ("length", "l", Match(Var("l"), Int(0), "x", "y", Op(Plus, Int(1), Apply(Var("length"), Var("y")))), 
         Apply(Var("length"), Cons(Int(1), Cons(Int(2), Cons(Int(3), Empty)))))
      
      LetRec
        ("length", "l", Match(Var("l"), Int(0), "x", "y", Op(Plus, Int(1), Apply(Var("length"), Var("y")))), 
         Apply
           (Var("length"), 
            Cons(Cons(Int(1), Cons(Int(2), Empty)), Cons(Cons(Int(3), Cons(Int(4), Cons(Int(5), Empty))), Empty))))
      
      LetRec
        ("append", "l1", 
         Fun
           ("l2", 
            Match(Var("l1"), Var("l2"), "x", "y", Cons(Var("x"), Apply(Apply(Var("append"), Var("y")), Var("l2"))))), 
         Apply(Apply(Var("append"), Cons(Int(1), Cons(Int(2), Empty))), Cons(Int(3), Cons(Int(4), Cons(Int(5), Empty)))))
      
      //|- let rec apply = fun l -> fun x ->      match l with [] -> x | f :: l -> f (apply l x) in    apply ((fun x -> x * x) :: (fun y -> y + 3) :: []) 4    evalto 49
      LetRec
        ("apply", "l", 
         Fun("x", Match(Var("l"), Var("x"), "f", "l", Apply(Var("f"), Apply(Apply(Var("apply"), Var("l")), Var("x"))))), 
         Apply
           (Apply
              (Var("apply"), 
               Cons(Fun("x", Op(Times, Var("x"), Var("x"))), Cons(Fun("y", Op(Plus, Var("y"), Int(3))), Empty))), Int(4)))
      
      // |- let rec apply = fun l -> fun x ->      match l with [] -> x | f :: l -> apply l (f x) in    apply ((fun x -> x * x) :: (fun y -> y + 3) :: []) 4    evalto 19
      LetRec
        ("apply", "l", 
         Fun("x", Match(Var("l"), Var("x"), "f", "l", Apply(Apply(Var("apply"), Var("l")), Apply(Var("f"), Var("x"))))), 
         Apply
           (Apply
              (Var("apply"), 
               Cons(Fun("x", Op(Times, Var("x"), Var("x"))), Cons(Fun("y", Op(Plus, Var("y"), Int(3))), Empty))), Int(4))) ]
  
  let g p = 
    eval [] p
    |> fst
    |> derivationToString
    |> fun x -> x.Replace("\t", "  ")
    |> printfn "\n%s\n"
  
  List.map g p |> ignore
  0 // 整数の終了コードを返します
