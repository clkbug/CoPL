// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat

type Nat = 
  | Zero
  | Succ of Nat

type Exp = 
  | Nat of Nat
  | Plus of Nat * Nat
  | Times of Nat * Nat
  | Add of Exp * Exp
  | Mul of Exp * Exp

type Judgment = 
  | Judgment of Exp * Nat

type Conclusion = Judgment

type Derivation = 
  | EConst of Conclusion
  | EPlus of Derivation * Derivation * Derivation * Conclusion
  | ETimes of Derivation * Derivation * Derivation * Conclusion
  | PZero of Conclusion
  | PSucc of Derivation * Conclusion
  | TZero of Conclusion
  | TSucc of Derivation * Derivation * Conclusion
  | False of Judgment

let rec natToInt n = 
  match n with
  | Zero -> 0
  | Succ(m) -> 1 + natToInt m

let rec intToNat n = 
  match n with
  | 0 -> Zero
  | _ -> Succ(intToNat (n - 1))

let tfold name x d f = 
  let a = production name
  a.rule <- a + x --> f |- d
  a

let spaces = tfold "spaces" ~~" " ~~"" (fun (x, y) -> x + y)
let ss x = spaces +. x .+ spaces

let parseJudgment s = 
  let nat = 
    let zero = ~~"Z" --> fun _ -> Zero
    let nonzero = production "nonzero"
    let nat = zero |- nonzero
    nonzero.rule <- ~~"S" + ~~"(" +. nat .+ ~~")" --> fun n -> Succ(n)
    nat
  
  let exp = production "exp"
  let term = production "term"
  let primary = production "primary"
  exp.rule <- (ss exp .+ ss ~~"+" + ss term --> Add) |- ss term
  term.rule <- (ss term .+ ss ~~"*" + ss primary --> Mul) |- ss primary
  primary.rule <- ss ~~"(" +. exp .+ ss ~~")" |- ss nat --> Nat
  let pj = exp .+ ss ~~"evalto" + nat --> Judgment
  match parse pj s with
  | Success x -> x.value
  | Failure _ -> failwith "parse failed"

let rec natToString n = 
  match n with
  | Zero -> "Z"
  | Succ x -> "S(" + natToString x + ")"

let rec expToString e = 
  match e with
  | Nat(n) -> natToString n
  | Add(e1, e2) -> "(" + expToString e1 + " + " + expToString e2 + ")"
  | Mul(e1, e2) -> "(" + expToString e1 + " * " + expToString e2 + ")"
  | Plus(a, b) -> 
    sprintf "%s plus %s is %s" (natToString a) (natToString b) ((natToInt a + natToInt b)
                                                                |> intToNat
                                                                |> natToString)
  | Times(a, b) -> 
    sprintf "%s times %s is %s" (natToString a) (natToString b) ((natToInt a * natToInt b)
                                                                 |> intToNat
                                                                 |> natToString)

let judgmentToString j = 
  match j with
  | Judgment(Plus(_, _) as e, n) | Judgment(Times(_, _) as e, n) -> expToString e
  | Judgment(e, n) -> expToString e + " evalto " + natToString n

let rec derivationToString d = 
  let indent (s : string) = "\t" + s.Replace("\n", "\n\t")
  let indDTS = derivationToString >> indent
  match d with
  | EConst(Judgment(Nat(n), m) as j) -> 
    if n = m then sprintf "%s by E-Const{};" (judgmentToString j)
    else derivationToString (False(j))
  | EPlus(d1, d2, d3, c) -> 
    sprintf "%s by E-Plus{\n%s\n%s\n%s\n};" (judgmentToString c) (indDTS d1) (indDTS d2) (indDTS d3)
  | ETimes(d1, d2, d3, c) -> 
    sprintf "%s by E-Times{\n%s\n%s\n%s\n};" (judgmentToString c) (indDTS d1) (indDTS d2) (indDTS d3)
  | PZero(c) -> sprintf "%s by P-Zero{};" (judgmentToString c)
  | PSucc(p, c) -> sprintf "%s by P-Succ{\n%s\n};" (judgmentToString c) (indent (derivationToString p))
  | TZero(c) -> sprintf "%s by T-Zero{};" (judgmentToString c)
  | TSucc(p1, p2, c) -> 
    sprintf "%s by T-Succ{\n%s\n%s\n};" (judgmentToString c) (indent (derivationToString p1)) 
      (indent (derivationToString p2))
  | False(j) -> sprintf "%s is not TRUE" (judgmentToString j)
  | _ -> failwith "にゃーん"

let rec eval e = 
  match e with
  | Nat(n) -> (EConst(Judgment(e, n)), n)
  | Plus(Zero, n) -> (PZero(Judgment(e, n)), n)
  | Plus(Succ(n1), n2) -> 
    let (d, n) = eval (Plus(n1, n2))
    (PSucc(d, Judgment(e, n)), Succ(n))
  | Times(Zero, n) -> (TZero(Judgment(e, n)), Zero)
  | Times(Succ(n1), n2) -> 
    let (d1, n3) = eval (Times(n1, n2))
    let (d2, n4) = eval (Plus(n2, n3))
    (TSucc(d1, d2, Judgment(e, n4)), n4)
  | Add(e1, e2) -> 
    let (d1, n1) = eval e1
    let (d2, n2) = eval e2
    let (d3, n) = eval (Plus(n1, n2))
    (EPlus(d1, d2, d3, Judgment(e, n)), n)
  | Mul(e1, e2) -> 
    let (d1, n1) = eval e1
    let (d2, n2) = eval e2
    let (d3, n) = eval (Times(n1, n2))
    (ETimes(d1, d2, d3, Judgment(e, n)), n)

[<EntryPoint>]
let main argv = 
  let f s = 
    match parseJudgment s with
    | Judgment(e, n) -> 
      eval e
      |> fst
      |> derivationToString
      |> printfn "\n%s\n"
  
  let propositions = 
    [ "Z + S(S(Z)) evalto S(S(Z))"; "S(S(Z)) + Z evalto S(S(Z))"; "S(Z) + S(Z) + S(Z) evalto S(S(S(Z)))"; 
      "S(S(S(Z))) + S(S(Z)) * S(Z) evalto S(S(S(S(S(Z)))))"; "(S(S(Z)) + S(S(Z))) * Z evalto Z"; 
      "Z * (S(S(Z)) + S(S(Z))) evalto Z" ]
  List.map f propositions |> ignore
//  while true do
//    stdin.ReadLine()
//    |> f
//    |> ignore
  0 // 整数の終了コードを返します

