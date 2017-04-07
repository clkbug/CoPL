// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat

type Nat = 
  | Zero
  | Succ of Nat

type Exp = 
  | Nat of Nat
  | Plus of Nat * Nat * Nat
  | Times of Nat * Nat * Nat
  | Add of Exp * Exp
  | Mul of Exp * Exp

type Judgment = 
  | JudgPeano of Exp
  | JudgR of Exp * Exp
  | JudgMR of Exp * Exp
  | JudgDR of Exp * Exp

type Conclusion = Judgment

type Derivation = 
  | PZero of Conclusion
  | PSucc of Derivation * Conclusion
  | TZero of Conclusion
  | TSucc of Derivation * Derivation * Conclusion
  | RPlus of Derivation * Conclusion
  | RPlusL of Derivation * Conclusion
  | RPlusR of Derivation * Conclusion
  | RTimes of Derivation * Conclusion
  | RTimesL of Derivation * Conclusion
  | RTimesR of Derivation * Conclusion
  | MRZero of Conclusion
  | MROne of Derivation * Conclusion
  | MRMulti of Derivation * Derivation * Conclusion
  | DRPlus of Derivation * Conclusion
  | DRPlusL of Derivation * Conclusion
  | DRPlusR of Derivation * Conclusion
  | DRTimes of Derivation * Conclusion
  | DRTimesL of Derivation * Conclusion
  | DRTimesR of Derivation * Conclusion
  | False of Judgment
  | Mu

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
  let r = exp .+ ss ~~"--->" + exp --> JudgR
  let mr = exp .+ ss ~~"-*->" + exp --> JudgMR
  let dr = exp .+ ss ~~"-d->" + exp --> JudgDR
  let pj = r |- mr |- dr
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
  | JudgR(e1, e2) -> expToString e1 + " ---> " + expToString e2
  | JudgMR(e1, e2) -> expToString e1 + " -*-> " + expToString e2
  | JudgDR(e1, e2) -> expToString e1 + " -d-> " + expToString e2

let rec derivationToString d = 
  let indent (s : string) = "\t" + s.Replace("\n", "\n\t")
  let indDTS = derivationToString >> indent
  match d with
  | PZero(c) -> sprintf "%s by P-Zero{};" (judgmentToString c)
  | PSucc(p, c) -> sprintf "%s by P-Succ{\n%s\n};" (judgmentToString c) (indent (derivationToString p))
  | TZero(c) -> sprintf "%s by T-Zero{};" (judgmentToString c)
  | TSucc(p1, p2, c) -> 
    sprintf "%s by T-Succ{\n%s\n%s\n};" (judgmentToString c) (indent (derivationToString p1)) 
      (indent (derivationToString p2))
  | False(j) -> sprintf "%s is not TRUE" (judgmentToString j)
  | _ -> failwith "にゃーん"

let rec isReducible e = 
  match e with
  | Nat(_) -> false
  | _ -> true

let rec prove j = 
  match j with
  | JudgPeano(Plus(Zero, n, m)) -> 
    if n = m then PZero(j)
    else False(j)
  | JudgPeano(Plus(Succ(n1), n2, Succ(n3))) -> PSucc(pjp (Plus(n1, n2, n3)), j)
  | JudgPeano(Times(Zero, _, Zero)) -> TZero(j)
  | JudgPeano(Times(Succ(n1), n2, n4)) -> 
    let n3 = intToNat (natToInt n1 * natToInt n2)
    TSucc(pjp (Times(n1, n2, n3)), pjp (Plus(n2, n3, n4)), j)
  | _ -> False(j)

and pjp = JudgPeano >> prove

let rec reduce j = 
  match j with
  | JudgR(Add(Nat(n1), Nat(n2)), Nat(n3)) -> (RPlus(pjp (Plus(n1, n2, n3)), j), Nat(n3))
  | JudgR(Mul(Nat(n1), Nat(n2)), Nat(n3)) -> (RTimes(pjp (Times(n1, n2, n3)), j), Nat(n3))
  | JudgR(Add(e1, e2) as e, (Add(e3, e4) as e')) -> 
    if e = e' then (Mu, e)
    else if e1 <> e3 then 
  | JudgDR(Add(Nat(n1), Nat(n2)), Nat(n3)) -> (RPlus(pjp (Plus(n1, n2, n3)), j), Nat(n3))
  //  | JudgDR(Add(Nat(n1), e2), Nat(n3)) -> DRPlusR()
  //  | JudgDR(Mul(Nat(n1), Nat(n2)), Nat(n3)) -> RTimes(pjp (Times(n1, n2, n3)), j)
  | _ -> failwith ""

[<EntryPoint>]
let main argv = 
  let f s = 
    let j = parseJudgment s
    printfn "\n%A\n" j
  
  let propositions = 
    [ "Z + S(S(Z)) -*-> S(S(Z))"; "S(Z) * S(Z) + S(Z) * S(Z) -d-> S(Z) + S(Z) * S(Z)"; 
      "S(Z) * S(Z) + S(Z) * S(Z) ---> S(Z) * S(Z) + S(Z)"; "S(Z) * S(Z) + S(Z) * S(Z) -*-> S(S(Z))" ]
  List.map f propositions |> ignore
  //  while true do
  //    stdin.ReadLine()
  //    |> f
  //    |> ignore
  0 // 整数の終了コードを返します

