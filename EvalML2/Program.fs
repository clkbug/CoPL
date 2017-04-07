// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat
open System

type BinOP = 
  | Plus
  | Minus
  | Times
  | LessThan

type Exp = 
  | Var of string
  | Int of int
  | Bool of bool
  | Op of BinOP * Exp * Exp
  | If of Exp * Exp * Exp
  | MetaOp of BinOP * Exp * Exp
  | Let of string * Exp * Exp

type Env = (string * Exp) list

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

let tfold name x d f = 
  let a = production name
  a.rule <- a + x --> f |- d
  a

let tfoldd name x f = tfold name x x f
let add = fun (x, y) -> x + y
//  空白
let space = oneOf " \t\n\r" --> fun c -> c.ToString()
let spaces = tfold "spaces" space ~~"" add
let spaces1 = tfold "spaces1" ~~"" space add
//  空白に挟まれた何か
let ss x = spaces +. x .+ spaces
let sxs x = spaces +. x .+ spaces
let sss s = sxs ~~s
let keyword s = spaces +. ~~s .+ spaces1

let parseJudgment s = 
  let digit = oneOf "0123456789" --> fun d -> Int(int (d) - int ('0'))
  let digits = production "digits"
  digits.rule <- (digits + digit --> fun x -> 
                    match x with
                    | (Int(a), Int(b)) -> Int(a * 10 + b)
                    | _ -> failwith "cant reach here")
                 |- digit
  let negative = 
    ~~"-" +. digits --> fun x -> 
      match x with
      | Int(n) -> Int(-n)
      | _ -> failwith "can't reach here"
  
  let int = ss negative |- ss digits
  let t = ss ~~"true" --> fun _ -> Bool(true)
  let f = ss ~~"false" --> fun _ -> Bool(false)
  
  //  Identifier
  let identifier = 
    let idHead = 
      oneOf (String.Concat(List.concat [ [ 'a'..'z' ]
                                         [ 'A'..'Z' ] ]))
      --> fun c -> c.ToString()
    
    let idTail = 
      oneOf (String.Concat(List.concat [ [ 'a'..'z' ]
                                         [ 'A'..'Z' ]
                                         [ '0'..'9' ]
                                         [ '_' ] ]))
      --> fun c -> c.ToString()
    
    tfold "identifier" idTail idHead add .+ spaces
  
  let var = identifier --> Var
  let v = int |- t |- f |- var
  let envVar = identifier .+ ss ~~"=" + v --> fun (x, y) -> (x, y)
  let envEnd = ss ~~"|-" --> fun _ -> []
  let env' = production "env'"
  env'.rule <- (envVar + (ss ~~"," +. env' |- envEnd) --> fun (x, y) -> x :: y) |- envEnd
  let env = env' --> List.rev
  let letexp = production "letexp"
  let ifexp = production "ifexp"
  let exp = production "exp"
  let additive = production "additive"
  let multitive = production "multitive"
  let primary = production "primary"
  letexp.rule <- (keyword "let" +. identifier .+ ss ~~"=" + letexp .+ keyword "in" + letexp 
                  --> fun ((x, y), z) -> Let(x, y, z)) |- ifexp
  ifexp.rule <- (ss ~~"if" +. ss exp .+ ss ~~"then" + ss exp .+ ss ~~"else" + ss exp --> fun ((x, y), z) -> If(x, y, z)) 
                |- ss exp
  exp.rule <- (ss exp .+ ss ~~"<" + ss additive --> fun (x, y) -> Op(LessThan, x, y)) |- ss additive
  additive.rule <- (ss additive + ss (oneOf "+-") + ss multitive --> fun ((x, y), z) -> Op(c2op y, x, z)) 
                   |- ss multitive
  multitive.rule <- (ss multitive .+ ss ~~"*" + ss primary --> fun (x, y) -> Op(Times, x, y)) |- ss primary
  primary.rule <- ss ~~"(" +. letexp .+ ss ~~")" |- ss v
  let pj = env + letexp .+ ss ~~"evalto" + ss v --> fun ((x, y), z) -> (x, y, z)
  match parse pj s with
  | Success x -> x.value
  | Failure x -> failwithf "parse failed\n%A" x

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

let envToString env = 
  let elemToString (name, v) = sprintf "%s = %s" name (expToString v)
  List.map elemToString env
  |> List.rev
  |> String.concat ", "

let rec derivationToString d = 
  let indent (s : string) = "\t" + s.Replace("\n", "\n\t")
  let indDTS = derivationToString >> indent
  match d with
  | EInt(env, Int(i), _) -> sprintf "%s |- %d evalto %d by E-Int{};" (envToString env) i i
  | EBool(env, b, _) -> sprintf "%s |- %s evalto %s by E-Bool{};" (envToString env) (expToString b) (expToString b)
  | EVar1(env, n, v) -> sprintf "%s |- %s evalto %s by E-Var1{};" (envToString env) (expToString n) (expToString v)
  | EVar2(d, (env, n, v)) -> 
    sprintf "%s |- %s evalto %s by E-Var2{\n%s\n};" (envToString env) (expToString n) (expToString v) (indDTS d)
  | EIfT(d1, d2, (env, exp, v)) -> 
    sprintf "%s |- %s evalto %s by E-IfT{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2)
  | EIfF(d1, d2, (env, exp, v)) -> 
    sprintf "%s |- %s evalto %s by E-IfF{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2)
  | EPlus(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s |- %s evalto %s by E-Plus{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | EMinus(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s |- %s evalto %s by E-Minus{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | ETimes(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s |- %s evalto %s by E-Times{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | ELt(d1, d2, d3, (env, exp, v)) -> 
    sprintf "%s |- %s evalto %s by E-Lt{\n%s\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) 
      (indDTS d1) (indDTS d2) (indDTS d3)
  | ELet(d1, d2, (env, exp, v)) -> 
    sprintf "%s |- %s evalto %s by E-Let{\n%s\n%s\n};" (envToString env) (expToString exp) (expToString v) (indDTS d1) 
      (indDTS d2)
  | BPlus(env, exp, v) -> sprintf "%s is %s by B-Plus{};" (expToString exp) (expToString v)
  | BMinus(env, exp, v) -> sprintf "%s is %s by B-Minus{};"  (expToString exp) (expToString v)
  | BTimes(env, exp, v) -> sprintf "%s is %s by B-Times{};" (expToString exp) (expToString v)
  | BLt(env, exp, v) -> sprintf "%s is %s by B-Lt{};" (expToString exp) (expToString v)
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
  | _ -> failwithf "can't reach here... in eval %A\n" exp

[<EntryPoint>]
let main argv = 
  let f s = 
    parseJudgment s
    |> (fun (x, y, _) -> eval x y)
    |> fst
    |> derivationToString
    |> printfn "\n%s\n"
  
  let propositions = 
    [ "x = 3, y = 2 |- x evalto 3"; "x = true, y = 4 |- if x then y + 1 else y - 1 evalto 5"; 
      "|- let x = 1 + 2 in x * 4 evalto 12"; "|- let x = (3 * 3) in (let y = 4 * x in x + y) evalto 45"; 
      "x = 3 |- let x = x * 2 in x + x evalto 12"; "|- let x = let y = 3 - 2 in y * y in let y = 4 in x + y evalto 5" ]
  List.map f propositions |> ignore
  //  while true do
  //    stdin.ReadLine()
  //    |> f
  //    |> ignore
  0 // 整数の終了コードを返します
