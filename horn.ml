open Typeform
open FormulaHorn
module SS = Set.Make(struct type t = Typeform.atomicformula let compare = Stdlib.compare end)
let singleton (x: atomicformula) : SS.t = SS.add x (let () = () in SS.empty)

let convertRStoAF (phi: rightside) : atomicformula =
  match phi with
  | RProp t -> if (t = (true )) then ATop else ABot
  | RVar x -> AVar x

let convertPLtoAF (phi: pliteral) : atomicformula =
  match phi with
  | LBottom -> ABot
  | LVar x -> AVar x

let convertAFtoPL (phi: atomicformula) : pliteral =
  match phi with
  | ATop -> assert false (* absurd *)
  | ABot -> LBottom
  | AVar x -> LVar x

let rec convertConjunctionToSet (phi: conj_pliteral) : SS.t =
  match phi with
  | CPL pl -> singleton (convertPLtoAF pl)
  | CPAnd (c1,
    c2) ->
    SS.union (convertConjunctionToSet c1) (convertConjunctionToSet c2)

let rec convertToSet (phi: leftside) : SS.t =
  match phi with
  | LTop -> singleton ATop
  | LPos c -> convertConjunctionToSet c

let rec convertToList (phi: hornclause) : ((SS.t) * rightside) list =
  match phi with
  | HBasic BImpl (l, r) -> (convertToSet l, r) :: [] 
  | HAnd (e1, e2) -> List.append (convertToList e1) (convertToList e2)

let rec findFirst (listformula: ((SS.t) * rightside) list) (s: SS.t) :
  (((SS.t) * rightside) list) * (((SS.t) * rightside) list) =
  match listformula with
  | [] -> ([] , [] )
  | (l, r) :: lst ->
    if SS.subset l s
    then ([] , (l, r) :: lst)
    else begin let (le, ri) = findFirst lst s in ((l, r) :: le, ri) end

let rec algorithmA (listformula: ((SS.t) * rightside) list) (s: SS.t) : 
  SS.t =
  match listformula with
  | [] -> s
  | _ ->
    (let (left, right) = findFirst listformula s in
     match right with
     | [] -> s
     | (_, r) :: lst ->
       algorithmA (List.append left lst) (SS.add (convertRStoAF r) s))

let rec processHorn (phi: ((SS.t) * rightside) list) (s: SS.t) : bool =
  let result_set = algorithmA phi s in
  if SS.mem ABot result_set then false  else true 

let horn (phi: hornclause) : bool =
  processHorn (convertToList phi) (singleton ATop)

