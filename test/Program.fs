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
  | Empty
  | Cons of Exp * Exp
  | Match of Exp * Exp * Name * Name * Exp

and Env = (string * Exp) list

type Type = 
  | TInt
  | TBool

type TEnv = (Name * Type) list

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

let tstfold name x s d f = 
  let a = production name
  a.rule <- a + s + x --> f |- d
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

let parser = 
  let digit = oneOf "0123456789" --> fun d -> Int(int (d) - int ('0'))
  let digits = production "digits"
  digits.rule <- (digits + digit --> fun x -> 
                    match x with
                    | (Int(a), Int(b)) -> Int(a * 10 + b)
                    | _ -> failwith "cant reach here")
                 |- digit
  let int = ss digits
  let t = ss ~~"true" --> fun _ -> Bool(true)
  let f = ss ~~"false" --> fun _ -> Bool(false)
  let e = ss ~~"[]" --> fun _ -> Empty
  
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
    
    tfoldd "identifier" (oneOf "abcdefghijklmnopqrstuvwxyz" --> fun c -> c.ToString()) add .+ spaces
  
  let var = identifier --> Var
  let binOpFun ((x, y), z) = Op(c2op y, x, z)
  let simpleExp = production "simpleExp"
  let exp = production "exp"
  let letexp = production "letexp"
  let funexp = production "funexp"
  let matchexp = production "matchexp"
  let ifexp = production "ifexp"
  let list = production "list"
  let rec comparative = tstfold "comparative" (ss additive) (oneOf "<") (ss additive) binOpFun
  and additive = tstfold "additive" (ss multitive) (oneOf "+-") (ss multitive) binOpFun
  and multitive = tstfold "multitive" (ss list) (oneOf "*") (ss list) binOpFun
  and apply = tfoldd "apply" (ss simpleExp) Apply
  exp.rule <- letexp
  letexp.rule <- (keyword "LET" +. identifier .+ ss ~~"=" + funexp .+ keyword "IN" + funexp 
                  --> fun ((x, y), z) -> Let(x, y, z)) 
                 |- (keyword "LET" + keyword "REC" +. identifier .+ ss ~~"=" .+ keyword "FUN" + identifier .+ ss ~~"->" 
                     + funexp .+ keyword "IN" + funexp --> fun (((x, y), z), w) -> LetRec(x, y, z, w)) |- funexp
  funexp.rule <- (keyword "FUN" +. identifier .+ ss ~~"->" + matchexp --> Fun) |- matchexp
  matchexp.rule <- (keyword "MATCH" +. ifexp .+ keyword "WITH" .+ e .+ ss ~~"->" + ifexp .+ ss ~~"|" + identifier 
                    .+ ss ~~"::" + identifier .+ ss ~~"->" + ifexp 
                    --> fun ((((e1, e2), n1), n2), e3) -> Match(e1, e2, n1, n2, e3)) |- ifexp
  ifexp.rule <- (keyword "IF" +. comparative .+ keyword "THEN" + comparative .+ keyword "ELSE" + comparative 
                 --> fun ((x, y), z) -> If(x, y, z)) |- comparative
  list.rule <- (apply .+ ss ~~"::" + list --> Cons) |- apply
  simpleExp.rule <- ss ~~"(" +. exp .+ ss ~~")" |- int |- e |- t |- f |- var
  let ty = (keyword "int" --> fun _ -> TInt) |- (keyword "bool" --> fun _ -> TBool)
  
  let env = 
    let a = identifier .+ ss ~~":" + ty
    let envend = ss ~~"|-" --> fun _ -> []
    let e = production "e"
    e.rule <- (a .+ ss ~~"," + e --> fun (x, y) -> x :: y) |- (a + envend --> fun (x, y) -> x :: y) |- envend
    e
  env + exp .+ ss ~~":" .+ ty

let preprocess (a : string) = 
  let reserved = [ "if"; "then"; "else"; "match"; "with"; "fun"; "let"; "in"; "rec" ]
  List.map (fun (x : string) -> (" " + x + " ", " " + x.ToUpper() + " ")) reserved
  |> List.fold (fun (s : string) (x, y) -> s.Replace(x, y)) (" " + a)
  |> fun x -> x + " "

[<EntryPoint>]
let main argv = 
  let p = 
    [ "|- 3 + 5"; "|- if 4 < 5 then 2 + 3 else 8 * 8"; "x : bool, y : int |- if x then y + 1 else y - 1"; 
      "|- let x = 3 < 2 in let y = 5 in if x then y else 2"; "|- fun x -> x + 1"; "|- let f = fun x -> x + 1 in f 4"; 
      "|- fun f -> f 0 + f 1"; "|- let max = fun x -> fun y -> if x < y then y else x in max 3 5"; "|- 4 :: []"; 
      "|- true :: false :: []"; "|- fun x -> fun y -> x"; "|- fun x -> fun y -> x"; 
      "|- let k = fun x -> fun y -> x in k 3 true"; "|- let k = fun x -> fun y -> x in k (1::[]) 3"; 
      "|- let k = fun x -> fun y -> x in k true (fun x -> x + 1)"; 
      "|- let compose = fun f -> fun g -> fun x -> f (g x) in   let p = fun x -> x * x in   let q = fun x -> x + 4 in   compose p q"; 
      "|- let compose = fun f -> fun g -> fun x -> f (g x) in   let p = fun x -> if x then 3 else 4 in   let q = fun x -> x < 4 in   compose p q"; 
      "|- let s = fun f -> fun g -> fun x -> f x (g x) in   let k1 = fun x -> fun y -> x in   let k2 = fun x -> fun y -> x in   s k1 k2"; 
      "|- let s = fun f -> fun g -> fun x -> f x (g x) in   let k1 = fun x -> fun y -> x in   let k2 = fun x -> fun y -> x in   s k1 k2 (fun x -> x + 1)"; 
      "|- let rec fact = fun n ->     if n < 2 then 1 else n * fact (n - 1) in     fact 3"; 
      "|- let rec sum = fun f -> fun n ->     if n < 1 then 0 else f n + sum f (n - 1) in    sum (fun x -> x * x) 2"; 
      "|- let l = (fun x -> x) :: (fun y -> 2) :: (fun z -> z + 3) :: [] in 2"; 
      "|- let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in    length"; 
      "|- let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in    length ((fun x -> x) :: (fun y -> y + 3) :: [])"; 
      "|- let rec append = fun l1 -> fun l2 ->      match l1 with [] -> l2 | x :: y -> x :: append y l2 in     append"; 
      "|- let rec append = fun l1 -> fun l2 ->      match l1 with [] -> l2 | x :: y -> x :: append y l2 in     append (true :: []) (false :: [])"; 
      "|- let rec map = fun f -> fun l ->     match l with [] -> [] | x :: y -> f x :: map f y in     map (fun x -> x < 3) (4 :: 5 :: 1 :: [])" ]
  while true do
    Console.ReadLine()
    |> preprocess
    |> fun x -> 
      printfn "%A" x
      x
      |> parse parser
      |> fun x -> 
        match x with
        | Success e -> printfn "Success:\n%A\n" e.value
        | Failure f -> printfn "Failure:\n%A\n" f
        |> ignore
  0 // 整数の終了コードを返します

