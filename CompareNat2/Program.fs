﻿// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat

type Nat = 
  | Zero
  | Succ of Nat

type Judgment = 
  | LessThan of Nat * Nat

type Conclusion = Judgment

type Derivation = 
  | LZero of Conclusion
  | LSuccSucc of Derivation * Conclusion
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
  
  let pj = nat .+ ~~" is less than " + nat --> LessThan
  match parse pj s with
  | Success x -> x.value
  | Failure _ -> failwith "parse failed"

let rec prove j = 
  match j with
  | LessThan(n, m) -> 
    match n with
    | Zero -> LZero(j)
    | Succ(x) -> 
      match m with
      | Succ(y) -> LSuccSucc(prove (LessThan(x, y)), j)
      | Zero -> False(j)

let rec natToString n = 
  match n with
  | Zero -> "Z"
  | Succ x -> "S(" + natToString x + ")"

let judgmentToString j = 
  match j with
  | LessThan(n, m) -> sprintf "%s is less than %s" (natToString n) (natToString m)

let rec derivationToString d = 
  match d with
  | LZero(c) -> sprintf "%s by L-Zero{};" (judgmentToString c)
  | LSuccSucc(p, c) -> 
    sprintf "%s by L-SuccSucc{\n%s\n};" (judgmentToString c) ("\t" + (derivationToString p).Replace("\n", "\n\t"))
  | False(j) -> sprintf "%s is not TRUE" (judgmentToString j)

[<EntryPoint>]
let main argv = 
  let f s = 
    parseJudgment s
    |> prove
    |> derivationToString
    |> printfn "\n%s\n"
  
  let propositions = [ "S(S(Z)) is less than S(S(S(Z)))"; "S(S(Z)) is less than S(S(S(S(S(Z)))))" ]
  List.map f propositions |> ignore
  0 // 整数の終了コードを返します

