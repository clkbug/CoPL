// F# の詳細については、http://fsharp.org を参照してください
// 詳細については、'F# チュートリアル' プロジェクトを参照してください。
open ScanRat
open System
open System.Collections.Generic

let counter = ref 0

let genId() = 
  incr counter
  !counter

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

type TyVar = 
  | TyVar of int

type Type = 
  | TInt
  | TBool
  | TFun of Type * Type
  | TList of Type
  | TVar of TyVar

type TyScheme = 
  | TST of Type
  | TSL of TyVar Set * Type

type TEnv = (Name * Type) list

type TySub = (Type * TyVar) list

type TEqu = TyScheme * TyScheme

type TJudg = TEnv * Exp * Type

type TDeriv = 
  | TDInt of TJudg
  | TDBool of TJudg
  | TDIf of TDeriv * TDeriv * TDeriv * TJudg
  | TDOp of BinOP * TDeriv * TDeriv * TJudg
  | TDVar of TJudg
  | TDLet of TDeriv * TDeriv * TJudg
  | TDFun of TDeriv * TJudg
  | TDApp of TDeriv * TDeriv * TJudg
  | TDLetRec of TDeriv * TDeriv * TJudg
  | TDNil of TJudg
  | TDCons of TJudg
  | TDMatch of TJudg

let rec extract tenv exp = 
  let newTyVar() = TVar(TyVar(genId()))
  match exp with
  | Int(_) -> Set.empty, TInt
  | Bool(_) -> Set.empty, TBool
  | Var(n) -> Set.empty, snd (List.find (fun x -> fst x = n) tenv)
  | Op(binOp, e1, e2) -> 
    let eq1, t1 = extract tenv e1
    let eq2, t2 = extract tenv e2
    
    let eq3 = 
      Set.union eq1 eq2 |> Set.union (Set.ofList [ (t1, TInt)
                                                   (t2, TInt) ])
    match binOp with
    | LessThan -> eq3, TBool
    | _ -> eq3, TInt
  | If(e1, e2, e3) -> 
    let eq1, t1 = extract tenv e1
    let eq2, t2 = extract tenv e2
    let eq3, t3 = extract tenv e3
    
    let eq4 = 
      Set.union eq1 eq2
      |> Set.union eq3
      |> Set.union (Set.ofList [ (t1, TBool)
                                 (t2, t3) ])
    eq4, t2
  | Let(n, e1, e2) -> 
    let eq1, t1 = extract tenv e1
    let eq2, t2 = extract ((n, t1) :: tenv) e2
    let eq3 = Set.union eq1 eq2
    eq3, t2
  | Fun(n, e) -> 
    let a = newTyVar()
    let eq, t0 = extract ((n, a) :: tenv) e
    eq, TFun(a, t0)
  | Apply(e1, e2) -> 
    let eq1, t1 = extract tenv e1
    let eq2, t2 = extract tenv e2
    let a = newTyVar()
    let eq3 = Set.union eq1 eq2 |> Set.add (t1, TFun(t2, a))
    eq3, a
  | LetRec(n1, n2, e1, e2) -> 
    let a1 = newTyVar()
    let a2 = newTyVar()
    let eq1, t1 = extract ((n2, a2) :: (n1, a1) :: tenv) e1
    let eq2, t2 = extract ((n1, a1) :: tenv) e2
    let eq3 = Set.union eq1 eq2 |> Set.add (a1, TFun(a2, t1))
    eq3, t2
  | Empty -> Set.empty, TList(newTyVar())
  | Cons(e1, e2) -> 
    let eq1, t1 = extract tenv e1
    let eq2, t2 = extract tenv e2
    let eq3 = Set.union eq1 eq2 |> Set.add (t2, TList(t1))
    eq3, t2
  | Match(e1, e2, x, y, e3) -> 
    let eq1, t1 = extract tenv e1
    let eq2, t2 = extract tenv e2
    let a = newTyVar()
    let eq3, t3 = extract ((y, TList(a)) :: (x, a) :: tenv) e3
    
    let eq4 = 
      Set.union eq1 eq2
      |> Set.union eq3
      |> Set.union (Set.ofList [ (t1, TList(a))
                                 (t2, t3) ])
    eq4, t2
  | _ -> failwith "hoge"

let rec FTV t = 
  match t with
  | TBool | TInt -> Set.empty
  | TVar(a) -> Set.empty.Add(a)
  | TFun(t1, t2) -> Set.union (FTV t1) (FTV t2)
  | TList(t) -> FTV t

let FTVTS ts = 
  match ts with
  | TST(t) -> FTV t
  | TSL(tvs, t) -> Set.difference (FTV(t)) tvs

let rec FTVTE tenv = 
  match tenv with
  | [] -> Set.empty
  | (_, t) :: xs -> Set.union (FTVTE xs) (FTV t)

let rec substitute tysub ty = 
  match ty with
  | TInt | TBool -> ty
  | TVar(TyVar(a)) -> 
    match List.tryFind (fun x -> snd x = TyVar(a)) tysub with
    | Some(x) -> fst x
    | None -> ty
  | TFun(t1, t2) -> TFun(substitute tysub t1, substitute tysub t2)
  | TList(t) -> TList(substitute tysub t)

let rec substituteEqs tysub e = 
  match e with
  | [] -> []
  | (x, y) :: es -> (substitute tysub x, substitute tysub y) :: substituteEqs tysub es

let composite1 tysub (ty, tv) = (substitute tysub ty, tv) :: tysub
let composite tysub tysub' = List.fold composite1 tysub tysub'

let unify = 
  let rec unify' = 
    function 
    | [] -> []
    | (TInt, TInt) :: eqs | (TBool, TBool) :: eqs -> unify' eqs
    | (TFun(x, y), TFun(z, w)) :: eqs -> unify' ((x, z) :: (y, w) :: eqs)
    | (TList(x), TList(y)) :: eqs -> unify' ((x, y) :: eqs)
    | (TVar(x), t) :: eqs | (t, TVar(x)) :: eqs -> 
      if Set.contains x (FTV(t)) && TVar(x) <> t then failwith "type error"
      else 
        let s = unify' (substituteEqs [ (t, x) ] eqs)
        composite1 s (t, x)
    | (a, b) :: eqs when a = b -> unify' eqs
    | _ -> failwith "Unify error"
  Set.toList >> unify'

let pt tenv exp = 
  let e, t = extract tenv exp
  let s = unify e
  (s, substitute s t)

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
  let identifier = tfoldd "identifier" (oneOf "abcdefghijklmnopqrstuvwxyz" --> fun c -> c.ToString()) add .+ spaces
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
  letexp.rule <- (keyword "LET" +. identifier .+ ss ~~"=" + funexp .+ keyword "IN" + letexp 
                  --> fun ((x, y), z) -> Let(x, y, z)) 
                 |- (keyword "LET" + keyword "REC" +. identifier .+ ss ~~"=" .+ keyword "FUN" + identifier .+ ss ~~"->" 
                     + funexp .+ keyword "IN" + funexp --> fun (((x, y), z), w) -> LetRec(x, y, z, w)) |- funexp
  funexp.rule <- (keyword "FUN" +. identifier .+ ss ~~"->" + funexp --> Fun) |- matchexp
  matchexp.rule <- (keyword "MATCH" +. ifexp .+ keyword "WITH" .+ e .+ ss ~~"->" + ifexp .+ ss ~~"|" + identifier 
                    .+ ss ~~"::" + identifier .+ ss ~~"->" + ifexp 
                    --> fun ((((e1, e2), n1), n2), e3) -> Match(e1, e2, n1, n2, e3)) |- ifexp
  ifexp.rule <- (keyword "IF" +. comparative .+ keyword "THEN" + comparative .+ keyword "ELSE" + comparative 
                 --> fun ((x, y), z) -> If(x, y, z)) |- comparative
  list.rule <- (apply .+ ss ~~"::" + list --> Cons) |- apply
  simpleExp.rule <- ss ~~"(" +. exp .+ ss ~~")" |- int |- e |- t |- f |- var
  let ty = (ss ~~"int" --> fun _ -> TInt) |- (ss ~~"bool" --> fun _ -> TBool)
  
  let env = 
    let a = identifier .+ ss ~~":" + ty
    let envend = ss ~~"|-" --> fun _ -> []
    let e = production "e"
    e.rule <- (a .+ ss ~~"," + e --> fun (x, y) -> x :: y) |- (a + envend --> fun (x, y) -> x :: y) |- envend
    e
  env + exp

let preprocess (a : string) = 
  let reserved = [ "if"; "then"; "else"; "match"; "with"; "fun"; "let"; "in"; "rec" ]
  List.map (fun (x : string) -> (" " + x + " ", " " + x.ToUpper() + " ")) reserved
  |> List.fold (fun (s : string) (x, y) -> s.Replace(x, y)) (" " + a.Replace("(", " ( ").Replace(")", " ) "))
  |> fun x -> x + " "

[<EntryPoint>]
let main argv = 
  let p = 
    [ //"|- 3 + 5"; "|- if 4 < 5 then 2 + 3 else 8 * 8"; //"x : bool, y : int |- if x then y + 1 else y - 1"; 
      //"|- let x = (3 < 2) in (let y = 5 in (if x then y else 2))"; 
      //"|- fun x -> x + 1"; "|- let f = fun x -> x + 1 in f 4"; 
      //"|- fun f -> f 0 + f 1"; 
      //"|- let max = (fun x -> (fun y -> (if x < y then y else x))) in (max 3 5)"; 
      //"|- 4 :: []";       "|- true :: false :: []"; 
      //"|- fun x -> (fun y -> x)"; "|- fun x -> fun y -> x"; 
      //"|- let k = fun x -> fun y -> x in k 3 true"; "|- let k = fun x -> fun y -> x in k (1::[]) 3"; 
      //"|- let k = fun x -> fun y -> x in k true (fun x -> x + 1)"; 
      //"|- let compose = (fun f -> fun g -> fun x -> f (g x)) in   (let p = (fun x -> x * x) in   (let q = (fun x -> x + 4) in   (compose p q)))"; 
      //"|- let compose = (fun f -> fun g -> fun x -> f (g x)) in   (let p = (fun x -> if x then 3 else 4) in   (let q = (fun x -> x < 4) in  ( compose p q)))"; 
//      "|- let s = (fun f -> fun g -> fun x -> f x (g x)) in   (let k1 = (fun x -> fun y -> x) in   (let k2 = (fun x -> fun y -> x) in   (s k1 k2)))"; 
//      "|- let s = fun f -> fun g -> fun x -> f x (g x) in   let k1 = fun x -> fun y -> x in   let k2 = fun x -> fun y -> x in   s k1 k2 (fun x -> x + 1)"; 
//      "|- let rec fact = fun n ->     if n < 2 then 1 else n * fact (n - 1) in     fact 3"; 
//      "|- let rec sum = fun f -> fun n ->     if n < 1 then 0 else f n + sum f (n - 1) in    sum (fun x -> x * x) 2"; 
//      "|- let l = (fun x -> x) :: (fun y -> 2) :: (fun z -> z + 3) :: [] in 2"; 
//      "|- let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in    length"; 
//      "|- let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in    length ((fun x -> x) :: (fun y -> y + 3) :: [])"; 
      "|- let rec append = fun l -> fun lt ->      (match l with [] -> lt | x :: y -> (x :: (append y lt))) in     append"; 
      "|- let rec append = fun l -> fun ll ->      match l with [] -> ll | x :: y -> x :: append y ll in     append (true :: []) (false :: [])"; 
      "|- let rec map = fun f -> fun l ->     match l with [] -> [] | x :: y -> f x :: map f y in     map (fun x -> x < 3) (4 :: 5 :: 1 :: [])" ]
  
  let f s = 
    preprocess s
    |> parse parser
    |> fun x -> 
      match x with
      | Success e -> printfn "Success:\n%A\n" e.value; printfn "%A : %A\n->%A\n" s (pt [] (snd (e.value))) (pt [] (snd (e.value)) |> snd); 
      | Failure f -> printfn "Failure:\n%A\n%A\n%A\n" f s (preprocess s)
  List.map f p |> ignore
  0 // 整数の終了コードを返します

