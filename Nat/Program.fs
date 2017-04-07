// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat

type Nat = 
  | Zero
  | Succ of Nat

type Judgment = 
  | Plus of Nat * Nat * Nat
  | Times of Nat * Nat * Nat

type Conclusion = Judgment

type Derivation = 
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

let parseJudgment s = 
  let nat = 
    let zero = ~~"Z" --> fun _ -> Zero
    let nonzero = production "nonzero"
    let nat = zero |- nonzero
    nonzero.rule <- ~~"S" + ~~"(" +. nat .+ ~~")" --> fun n -> Succ(n)
    nat
  
  let plus = nat .+ ~~" plus " + nat .+ ~~" is " + nat --> fun ((x, y), z) -> Plus(x, y, z)
  let times = nat .+ ~~" times " + nat .+ ~~" is " + nat --> fun ((x, y), z) -> Times(x, y, z)
  let pj = plus |- times
  match parse pj s with
  | Success x -> x.value
  | Failure _ -> failwith "parse failed"

let rec prove j = 
  match j with
  | Plus(Zero, n, m) -> 
    if n = m then PZero(j)
    else False(j)
  | Plus(Succ(n1), n2, Succ(n3)) -> PSucc(prove (Plus(n1, n2, n3)), j)
  | Times(Zero, _, Zero) -> TZero(j)
  | Times(Succ(n1), n2, n4) -> 
    let n3 = intToNat (natToInt n1 * natToInt n2)
    TSucc(prove (Times(n1, n2, n3)), prove (Plus(n2, n3, n4)), j)
  | _ -> False(j)

let rec natToString n = 
  match n with
  | Zero -> "Z"
  | Succ x -> "S(" + natToString x + ")"

let JudgmentToString j = 
  match j with
  | Plus(a, b, c) -> sprintf "%s plus %s is %s" (natToString a) (natToString b) (natToString c)
  | Times(a, b, c) -> sprintf "%s times %s is %s" (natToString a) (natToString b) (natToString c)

let rec derivationToString d = 
  match d with
  | PZero(c) -> sprintf "%s by P-Zero{};" (JudgmentToString c)
  | PSucc(p, c) -> 
    sprintf "%s by P-Succ{\n%s\n};" (JudgmentToString c) ("\t" + (derivationToString p).Replace("\n", "\n\t"))
  | TZero(c) -> sprintf "%s by T-Zero{};" (JudgmentToString c)
  | TSucc(p1, p2, c) -> 
    sprintf "%s by T-Succ{\n%s\n%s\n};" (JudgmentToString c) ("\t" + (derivationToString p1).Replace("\n", "\n\t")) 
      ("\t" + (derivationToString p2).Replace("\n", "\n\t"))
  | False(j) -> sprintf "%s is not TRUE" (JudgmentToString j)

[<EntryPoint>]
let main argv = 
  let f s = 
    parseJudgment s
    |> prove
    |> derivationToString
    |> printfn "\n%s\n"
  
  let propositions = 
    [ "Z plus Z is Z"; "Z plus S(S(Z)) is S(S(Z))"; "S(S(Z)) plus Z is S(S(Z))"; "S(Z) plus S(S(S(Z))) is S(S(S(S(Z))))"; 
      "Z times S(S(Z)) is Z"; "S(S(Z)) times Z is Z"; "S(S(Z)) times S(Z) is S(S(Z))"; 
      "S(S(Z)) times S(S(Z)) is S(S(S(S(Z))))" ]
  List.map f propositions |> ignore
  stdin.Read() |> ignore
  0 // 整数の終了コードを返します
