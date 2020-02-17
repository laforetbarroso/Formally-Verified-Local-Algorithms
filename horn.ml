open Typeform
open FormulaHorn
module SS = Set.Make(struct type t = Typeform.atomicformula let compare = Stdlib.compare end)
let singleton (x: atomicformula) : SS.t = SS.add x (let () = () in SS.empty)

let rec eval_setconjunction (s: SS.t) (f: (string) -> (bool)) : bool =
  if SS.is_empty s
  then true 
  else
    begin
      let x = SS.choose s in
      ((eval_atomicformula x f) && (eval_setconjunction (SS.remove x s) f)) end

let rec convertRStoAF (phi: rightside) : atomicformula =
  match phi with
  | RProp t -> if (t = (true )) then ATop else ABot
  | RVar x -> AVar x

let rec convertPLtoAF (phi: pliteral) : atomicformula =
  match phi with
  | LBottom -> ABot
  | LVar x -> AVar x

let rec convertConjunctionToSet (phi: conj_pliteral) : SS.t =
  match phi with
  | CPL pl -> SS.add (convertPLtoAF pl) (let () = () in SS.empty)
  | CPAnd (c1,
    c2) ->
    SS.union (convertConjunctionToSet c1) (convertConjunctionToSet c2)

let rec convertToSet (phi: leftside) : SS.t =
  match phi with
  | LTop -> SS.add ATop (let () = () in SS.empty)
  | LPos c -> convertConjunctionToSet c

let rec convertToList (phi: hornclause) : ((SS.t) * rightside) list =
  match phi with
  | HBasic BImpl (l, r) -> (convertToSet l, r) :: [] 
  | HAnd (e1, e2) -> List.append (convertToList e1) (convertToList e2)

