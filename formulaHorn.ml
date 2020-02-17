type rightside =
  | RProp of bool
  | RVar of string

type pliteral =
  | LBottom
  | LVar of string

type conj_pliteral =
  | CPL of pliteral
  | CPAnd of conj_pliteral * conj_pliteral

type leftside =
  | LTop
  | LPos of conj_pliteral

type basichornclause =
  | BImpl of leftside * rightside

type hornclause =
  | HBasic of basichornclause
  | HAnd of hornclause * hornclause

