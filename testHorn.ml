open Horn
open Typeform
open FormulaHorn
open Format
let pp_rightside f =
  let rec pp_rightside = function
    | RProp x -> if x then "⊤" else "⊥"
    | RVar x -> Printf.sprintf "%s" x in
  Printf.sprintf "%s" (pp_rightside f)

let pp_pliteral f =
  let rec pp_pliteral = function
    | LBottom -> "⊥"
    | LVar x -> Printf.sprintf "%s" x in
  Printf.sprintf "%s" (pp_pliteral f)

let pp_conj_pliteral f =
  let rec pp_conj_pliteral = function
    | CPL x -> pp_pliteral x
  	| CPAnd (f1, f2) -> Printf.sprintf "(%s /\\ %s)" (pp_conj_pliteral f1) (pp_conj_pliteral f2) in
  Printf.sprintf "%s" (pp_conj_pliteral f)

let pp_leftside f =
  let rec pp_leftside = function
    | LTop -> "⊤"
  	| LPos x -> pp_conj_pliteral x in
  Printf.sprintf "%s" (pp_leftside f)


let pp_basichornclause f =
  let rec pp_basichornclause = function
    | BImpl (f1,f2) -> Printf.sprintf "(%s -> %s)" (pp_leftside f1) (pp_rightside f2) in
  Printf.sprintf "%s" (pp_basichornclause f)

let pp_hornclause f =
  let rec pp_hornclause = function
    | HBasic b -> pp_basichornclause b
    | HAnd (f1, f2) ->
        Printf.sprintf "(%s /\\ %s)" (pp_hornclause f1) (pp_hornclause f2) in
  Printf.sprintf "%s\n" (pp_hornclause f)



let pp_atomicformula f =
  let rec pp_atomicformula = function
    | ATop -> "⊤"
    | ABot -> "⊥"
    | AVar x -> Printf.sprintf "%s" x in
  Printf.sprintf "%s" (pp_atomicformula f)


let rec string_of_list = function
	| [] -> ""
	| e::[] ->(pp_atomicformula e)
	| e::l -> (pp_atomicformula e) ^ "," ^ string_of_list l


let string_of_set set = 
    print_string (string_of_list (SS.elements  set))

let rec print_element = function
	| (s,af) -> print_string "\t(["; string_of_set s ; print_string "]," ; print_string (pp_rightside af); print_string ")"


let rec print_list = function 
	| [] -> ()
	| e::[] -> print_element e; print_string "\n"
	| e::l -> print_element e; print_string ",\n" ; print_list l


let print_fancylist l =
	print_string "[\n"; print_list l; print_string "]\n"

let lvarp = LVar ("p")
let lvarr = LVar "r" 
let lvars = LVar "s"
let lvarq = LVar "q"
let lvart = LVar "t"

let rvarp = RVar "p"
let rvarr = RVar "r"
let rvars = RVar "s"
let rvarq = RVar "q"
let rvart = RVar "t"

let rtop = RProp true
let rbot = RProp false

let ex1() =

	let top_p = HBasic( BImpl (LTop , rvarp)) in
	let r_s = HBasic (BImpl (LPos (CPL lvarr), rvars)) in
	let pq_r = HBasic (BImpl (LPos (CPAnd (CPL lvarp, CPL lvarq)), rvarr)) in
	let rs_bot = HBasic (BImpl (LPos (CPAnd (CPL lvarr, CPL lvars)), rbot)) in
	let t_q = HBasic (BImpl (LTop, rvarq)) in
	let formula = HAnd (HAnd( top_p, r_s) , HAnd(HAnd(pq_r,rs_bot) , t_q)) in

	print_string "\n------------------- Exercice 1 --------------------\n";
	print_string "\nFormula:\n";
	print_string (pp_hornclause formula);

	print_string "\nHorn Result:\n";
	printf "%b\n%!" (horn(formula));
	print_string "\n---------------- End of Exercice 1 ----------------\n"


let ex2() =

	
	let top_p = HBasic( BImpl (LTop , rvarp)) in
	let r_s = HBasic (BImpl (LPos (CPL lvarr), rvars)) in
	let pq_r = HBasic (BImpl (LPos (CPAnd (CPL lvarp, CPL lvarq)), rvarr)) in
	let rs_bot = HBasic (BImpl (LPos (CPAnd (CPL lvarr, CPL lvars)), rbot)) in
	let formula = HAnd (HAnd( top_p, r_s) , HAnd(pq_r,rs_bot)) in

	print_string "\n------------------- Exercice 2 --------------------\n";
	print_string "\nFormula:\n";
	print_string (pp_hornclause formula);

	print_string "\nHorn Result:\n";
	printf "%b\n%!" (horn(formula));
	print_string "\n---------------- End of Exercice 2 ----------------\n"

let ex3() =

	
	let top_p = HBasic( BImpl (LTop , rvarp)) in
	let r_s = HBasic (BImpl (LPos (CPL lvarr), rvars)) in
	let p_r = HBasic (BImpl (LPos (CPL lvarp), rvarr)) in
	let r_bot = HBasic (BImpl (LPos (CPL lvarr), rbot)) in
	let formula = HAnd (HAnd( top_p, r_s) , HAnd(p_r,r_bot)) in

	print_string "\n------------------- Exercice 3 --------------------\n";
	print_string "\nFormula:\n";
	print_string (pp_hornclause formula);

	print_string "\nHorn Result:\n";
	printf "%b\n%!" (horn(formula));
	print_string "\n---------------- End of Exercice 3 ----------------\n"

let () =
	 ex1();
	 ex2();
	 ex3()