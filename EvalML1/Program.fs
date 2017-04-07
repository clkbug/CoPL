// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat

type BinOP = 
  | Plus
  | Minus
  | Times
  | LessThan

type Exp = 
  | Int of int
  | Bool of bool
  | Op of BinOP * Exp * Exp
  | If of Exp * Exp * Exp
  | MetaOp of BinOP * Exp * Exp

type Judgment = 
  | Judgment of Exp * Exp

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

let spaces = tfold "spaces" ~~" " ~~"" (fun (x, y) -> x + y)
let ss x = spaces +. x .+ spaces

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
  let v = int |- t |- f
  let ifexp = production "ifexp"
  let exp = production "exp"
  let additive = production "additive"
  let multitive = production "multitive"
  let primary = production "primary"
  ifexp.rule <- (ss ~~"if" +. ss exp .+ ss ~~"then" + ss exp .+ ss ~~"else" + ss exp --> fun ((x, y), z) -> If(x, y, z)) 
                |- ss exp
  exp.rule <- (ss exp .+ ss ~~"<" + ss additive --> fun (x, y) -> Op(LessThan, x, y)) |- ss additive
  additive.rule <- (ss additive + ss (oneOf "+-") + ss multitive --> fun ((x, y), z) -> Op(c2op y, x, z)) 
                   |- ss multitive
  multitive.rule <- (ss multitive .+ ss ~~"*" + ss primary --> fun (x, y) -> Op(Times, x, y)) |- ss primary
  primary.rule <- ss ~~"(" +. ifexp .+ ss ~~")" |- ss v
  let pj = ifexp .+ ss ~~"evalto" + ss v --> Judgment
  match parse pj s with
  | Success x -> x.value
  | Failure x -> failwithf "parse failed\n%A" x

let rec expToString e = 
  match e with
  | Int(n) -> string n
  | Bool(b) -> if b then "true" else "false"
  | Op(op, e1, e2) -> sprintf "(%s %s %s)" (expToString e1) (op2s op) (expToString e2)
  | If(e1, e2, e3) -> sprintf "(if %s then %s else %s)" (expToString e1) (expToString e2) (expToString e3)
  | MetaOp(op, e1, e2) -> sprintf "%s %s %s" (expToString e1) (op2ws op) (expToString e2)

let rec derivationToString d = 
  let indent (s : string) = "\t" + s.Replace("\n", "\n\t")
  let indDTS = derivationToString >> indent
  match d with
  | EInt(Judgment(Int(i), _)) -> sprintf "%d evalto %d by E-Int{};" i i
  | EBool(Judgment(b, _)) -> sprintf "%s evalto %s by E-Bool{};" (expToString b) (expToString b)
  | EIfT(d1, d2, Judgment(e, v)) -> 
    sprintf "%s evalto %s by E-IfT{\n%s\n%s\n};" (expToString e) (expToString v) (indDTS d1) (indDTS d2)
  | EIfF(d1, d2, Judgment(e, v)) -> 
    sprintf "%s evalto %s by E-IfF{\n%s\n%s\n};" (expToString e) (expToString v) (indDTS d1) (indDTS d2)
  | EPlus(d1, d2, d3, Judgment(e, v)) -> 
    sprintf "%s evalto %s by E-Plus{\n%s\n%s\n%s\n};" (expToString e) (expToString v) (indDTS d1) (indDTS d2) 
      (indDTS d3)
  | EMinus(d1, d2, d3, Judgment(e, v)) -> 
    sprintf "%s evalto %s by E-Minus{\n%s\n%s\n%s\n};" (expToString e) (expToString v) (indDTS d1) (indDTS d2) 
      (indDTS d3)
  | ETimes(d1, d2, d3, Judgment(e, v)) -> 
    sprintf "%s evalto %s by E-Times{\n%s\n%s\n%s\n};" (expToString e) (expToString v) (indDTS d1) (indDTS d2) 
      (indDTS d3)
  | ELt(d1, d2, d3, Judgment(e, v)) -> 
    sprintf "%s evalto %s by E-Lt{\n%s\n%s\n%s\n};" (expToString e) (expToString v) (indDTS d1) (indDTS d2) (indDTS d3)
  | BPlus(Judgment(e, v)) -> sprintf "%s is %s by B-Plus{};" (expToString e) (expToString v)
  | BMinus(Judgment(e, v)) -> sprintf "%s is %s by B-Minus{};" (expToString e) (expToString v)
  | BTimes(Judgment(e, v)) -> sprintf "%s is %s by B-Times{};" (expToString e) (expToString v)
  | BLt(Judgment(e, v)) -> sprintf "%s is %s by B-Lt{};" (expToString e) (expToString v)
  | _ -> failwith "can't reach here..."

let rec eval e = 
  match e with
  | Int(_) -> (EInt(Judgment(e, e)), e)
  | Bool(_) -> (EBool(Judgment(e, e)), e)
  | If(e1, e2, e3) -> 
    let (d1, v1) = eval e1
    if v1 = Bool(true) then 
      let (d2, v2) = eval e2
      (EIfT(d1, d2, Judgment(e, v2)), v2)
    else 
      let (d3, v3) = eval e3
      (EIfF(d1, d3, Judgment(e, v3)), v3)
  | Op(op, e1, e2) -> 
    let (d1, v1) = eval e1
    let (d2, v2) = eval e2
    let (d3, v3) = eval (MetaOp(op, v1, v2))
    
    let d = 
      match op with
      | Plus -> EPlus
      | Minus -> EMinus
      | Times -> ETimes
      | LessThan -> ELt
    (d (d1, d2, d3, Judgment(e, v3)), v3)
  | MetaOp(Plus, Int(n1), Int(n2)) -> (BPlus(Judgment(e, Int(n1 + n2))), Int(n1 + n2))
  | MetaOp(Minus, Int(n1), Int(n2)) -> (BMinus(Judgment(e, Int(n1 - n2))), Int(n1 - n2))
  | MetaOp(Times, Int(n1), Int(n2)) -> (BTimes(Judgment(e, Int(n1 * n2))), Int(n1 * n2))
  | MetaOp(LessThan, Int(n1), Int(n2)) -> (BLt(Judgment(e, Bool(n1 < n2))), Bool(n1 < n2))
  | _ -> failwithf "can't reach here... in eval %A\n" e

[<EntryPoint>]
let main argv = 
  let f s = 
    parseJudgment s
    |> (fun (Judgment(x, _)) -> x)
    |> eval
    |> fst
    |> derivationToString
    |> printfn "\n%s\n"
  

  let propositions = 
    [ "3 + 5 evalto 8"; "8 - 2 - 3 evalto 3"; "(4 + 5) * (1 - 10) evalto -81"; "if 4 < 5 then 2 + 3 else 8 * 8 evalto 5"; 
      "3 + (if -23 < -2 * 8 then 8 else 2 + 4) evalto 11"; "3 + (if -23 < -2 * 8 then 8 else 2) + 4 evalto 15" ]
  List.map f propositions |> ignore
  //  while true do
  //    stdin.ReadLine()
  //    |> f
  //    |> ignore
  0 // 整数の終了コードを返します
