type ident

type formula =
  | FVar of ident
  | FConst of bool
  | FAnd of formula * formula
  | FOr of formula * formula
  | FImpl of formula * formula
  | FNeg of formula

type formula_wi =
  | FVar_wi of ident
  | FConst_wi of bool
  | FAnd_wi of formula_wi * formula_wi
  | FOr_wi of formula_wi * formula_wi
  | FNeg_wi of formula_wi

type impl_kont =
  | KImpl_Id
  | KImpl_Neg of impl_kont * formula
  | KImpl_OrLeft of formula * impl_kont
  | KImpl_OrRight of impl_kont * formula_wi
  | KImpl_AndLeft of formula * impl_kont
  | KImpl_AndRight of impl_kont * formula_wi
  | KImpl_ImplLeft of formula * impl_kont
  | KImpl_ImplRight of impl_kont * formula_wi

type nnfc_kont =
  | Knnfc_id
  | Knnfc_negneg of nnfc_kont * formula_wi
  | Knnfc_negandleft of formula_wi * nnfc_kont
  | Knnfc_negandright of nnfc_kont * formula_wi
  | Knnfc_negorleft of formula_wi * nnfc_kont
  | Knnfc_negorright of nnfc_kont * formula_wi
  | Knnfc_andleft of formula_wi * nnfc_kont
  | Knnfc_andright of nnfc_kont * formula_wi
  | Knnfc_orleft of formula_wi * nnfc_kont
  | Knnfc_orright of nnfc_kont * formula_wi

type distr_kont =
  | KDistr_Id
  | KDistr_Left of formula_wi * formula_wi * distr_kont
  | KDistr_Right of distr_kont * formula_wi

type wf_distr_kont = distr_kont

type cnfc_kont =
  | KCnfc_Id
  | KCnfc_OrLeft of formula_wi * cnfc_kont
  | KCnfc_OrRight of cnfc_kont * formula_wi
  | KCnfc_AndLeft of formula_wi * cnfc_kont
  | KCnfc_AndRight of cnfc_kont * formula_wi

type wf_cnfc_kont = cnfc_kont

let rec impl_free_desf_cps (phi: formula) (k: impl_kont) : formula_wi =
  begin match phi with
  | FNeg phi1 -> impl_free_desf_cps phi1 (KImpl_Neg (k, phi1))
  | FOr (phi1, phi2) -> impl_free_desf_cps phi1 (KImpl_OrLeft (phi2, k))
  | FAnd (phi1, phi2) -> impl_free_desf_cps phi1 (KImpl_AndLeft (phi2, k))
  | FImpl (phi1, phi2) -> impl_free_desf_cps phi1 (KImpl_ImplLeft (phi2, k))
  | FConst phi1 -> impl_apply (FConst_wi phi1) k
  | FVar phi1 -> impl_apply (FVar_wi phi1) k
  end
and impl_apply (phi: formula_wi) (k: impl_kont) : formula_wi =
  begin match k with
  | KImpl_Id -> phi
  | KImpl_Neg (k1, phi1) -> impl_apply (FNeg_wi phi) k1
  | KImpl_OrLeft (phi1, k1) ->
    impl_free_desf_cps phi1 (KImpl_OrRight (k1, phi))
  | KImpl_OrRight (k1, phi2) -> impl_apply (FOr_wi (phi2, phi)) k1
  | KImpl_AndLeft (phi1, k1) ->
    impl_free_desf_cps phi1 (KImpl_AndRight (k1, phi))
  | KImpl_AndRight (k1, phi2) -> impl_apply (FAnd_wi (phi2, phi)) k1
  | KImpl_ImplLeft (phi1, k1) ->
    impl_free_desf_cps phi1 (KImpl_ImplRight (k1, phi))
  | KImpl_ImplRight (k1, phi2) ->
    impl_apply (FOr_wi ((FNeg_wi phi2), phi)) k1
  end

let rec impl_desf_main (phi: formula) : formula_wi =
  impl_free_desf_cps phi KImpl_Id

let rec nnfc_desf_cps (phi: formula_wi) (k: nnfc_kont) : formula_wi =
  begin match phi with
  | FNeg_wi FNeg_wi phi1 -> nnfc_desf_cps phi1 (Knnfc_negneg (k, phi1))
  | FNeg_wi FAnd_wi (phi1, phi2) ->
    nnfc_desf_cps (FNeg_wi phi1) (Knnfc_negandleft (phi2, k))
  | FNeg_wi FOr_wi (phi1, phi2) ->
    nnfc_desf_cps (FNeg_wi phi1) (Knnfc_negorleft (phi2, k))
  | FOr_wi (phi1, phi2) -> nnfc_desf_cps phi1 (Knnfc_orleft (phi2, k))
  | FAnd_wi (phi1, phi2) -> nnfc_desf_cps phi1 (Knnfc_andleft (phi2, k))
  | phi1 -> nnfc_apply phi1 k
  end
and nnfc_apply (phi: formula_wi) (k: nnfc_kont) : formula_wi =
  begin match k with
  | Knnfc_id -> phi
  | Knnfc_negneg (k1, phi1) -> nnfc_apply phi k1
  | Knnfc_negandleft (phi1, k1) ->
    nnfc_desf_cps (FNeg_wi phi1) (Knnfc_negandright (k1, phi))
  | Knnfc_negandright (k1, phi2) -> nnfc_apply (FOr_wi (phi2, phi)) k1
  | Knnfc_negorleft (phi1, k1) ->
    nnfc_desf_cps (FNeg_wi phi1) (Knnfc_negorright (k1, phi))
  | Knnfc_negorright (k1, phi2) -> nnfc_apply (FAnd_wi (phi2, phi)) k1
  | Knnfc_andleft (phi1, k1) -> nnfc_desf_cps phi1 (Knnfc_andright (k1, phi))
  | Knnfc_andright (k1, phi2) -> nnfc_apply (FAnd_wi (phi2, phi)) k1
  | Knnfc_orleft (phi1, k1) -> nnfc_desf_cps phi1 (Knnfc_orright (k1, phi))
  | Knnfc_orright (k1, phi2) -> nnfc_apply (FOr_wi (phi2, phi)) k1
  end

let nnfc_desf_main (phi: formula_wi) : formula_wi =
  nnfc_desf_cps phi Knnfc_id

let rec distr_desf_cps (phi1: formula_wi) (phi2: formula_wi)
                       (k: wf_distr_kont) : formula_wi =
  begin match (phi1, phi2) with
  | (FAnd_wi (phi11, phi12), phi21) ->
    distr_desf_cps phi11 phi21 (KDistr_Left (phi12, phi21, k))
  | (phi11, FAnd_wi (phi21, phi22)) ->
    distr_desf_cps phi11 phi21 (KDistr_Left (phi11, phi22, k))
  | (phi11, phi21) -> distr_apply (FOr_wi (phi11, phi21)) k
  end
and distr_apply (phi: formula_wi) (k: wf_distr_kont) : formula_wi =
  begin match k with
  | KDistr_Id -> phi
  | KDistr_Left (phi1, phi2, k1) ->
    distr_desf_cps phi1 phi2 (KDistr_Right (k1, phi))
  | KDistr_Right (k1, phi1) -> distr_apply (FAnd_wi (phi1, phi)) k1
  end

let distr_desf_main (phi1: formula_wi) (phi2: formula_wi) : formula_wi =
  distr_desf_cps phi1 phi2 KDistr_Id

let rec cnfc_desf_cps (phi: formula_wi) (k: wf_cnfc_kont) : formula_wi =
  begin match phi with
  | FOr_wi (phi1, phi2) -> cnfc_desf_cps phi1 (KCnfc_OrLeft (phi2, k))
  | FAnd_wi (phi1, phi2) -> cnfc_desf_cps phi1 (KCnfc_AndLeft (phi2, k))
  | phi1 -> cnfc_apply phi1 k
  end
and cnfc_apply (phi: formula_wi) (k: wf_cnfc_kont) : formula_wi =
  begin match k with
  | KCnfc_Id -> phi
  | KCnfc_OrLeft (phi1, k1) -> cnfc_desf_cps phi1 (KCnfc_OrRight (k1, phi))
  | KCnfc_OrRight (k1, phi2) ->
    let o = distr_desf_cps phi2 phi KDistr_Id in cnfc_apply o k1
  | KCnfc_AndLeft (phi1, k1) -> cnfc_desf_cps phi1 (KCnfc_AndRight (k1, phi))
  | KCnfc_AndRight (k1, phi2) -> cnfc_apply (FAnd_wi (phi2, phi)) k1
  end

let cnfc_desf_main (phi: formula_wi) : formula_wi =
  cnfc_desf_cps phi KCnfc_Id

let t (phi: formula) : formula_wi =
  let o = let o1 = impl_desf_main phi in nnfc_desf_main o1 in
  cnfc_desf_main o

let rec impl_free (phi: formula) : formula_wi =
  begin match phi with
  | FNeg phi1 -> FNeg_wi (impl_free phi1)
  | FOr (phi1, phi2) -> FOr_wi ((impl_free phi1), (impl_free phi2))
  | FAnd (phi1, phi2) -> FAnd_wi ((impl_free phi1), (impl_free phi2))
  | FImpl (phi1, phi2) ->
    FOr_wi ((FNeg_wi (impl_free phi1)), (impl_free phi2))
  | FConst phi1 -> FConst_wi phi1
  | FVar phi1 -> FVar_wi phi1
  end

let rec nnfc (phi: formula_wi) : formula_wi =
  begin match phi with
  | FNeg_wi FNeg_wi phi1 -> nnfc phi1
  | FNeg_wi FAnd_wi (phi1, phi2) ->
    FOr_wi ((nnfc (FNeg_wi phi1)), (nnfc (FNeg_wi phi2)))
  | FNeg_wi FOr_wi (phi1, phi2) ->
    FAnd_wi ((nnfc (FNeg_wi phi1)), (nnfc (FNeg_wi phi2)))
  | FOr_wi (phi1, phi2) -> FOr_wi ((nnfc phi1), (nnfc phi2))
  | FAnd_wi (phi1, phi2) -> FAnd_wi ((nnfc phi1), (nnfc phi2))
  | phi1 -> phi1
  end

let rec distr (phi1: formula_wi) (phi2: formula_wi) : formula_wi =
  begin match (phi1, phi2) with
  | (FAnd_wi (phi11, phi12), phi21) ->
    FAnd_wi ((distr phi11 phi21), (distr phi12 phi21))
  | (phi11, FAnd_wi (phi21, phi22)) ->
    FAnd_wi ((distr phi11 phi21), (distr phi11 phi22))
  | (phi11, phi21) -> FOr_wi (phi11, phi21)
  end

let rec cnfc (phi: formula_wi) : formula_wi =
  begin match phi with
  | FOr_wi (phi1, phi2) -> distr (cnfc phi1) (cnfc phi2)
  | FAnd_wi (phi1, phi2) -> FAnd_wi ((cnfc phi1), (cnfc phi2))
  | phi1 -> phi1
  end

let t1 (phi: formula) : formula_wi = cnfc (nnfc (impl_free phi))

let rec impl_free_cps : type a . formula -> (formula_wi -> a) ->  a =
  fun phi k -> 
    begin match phi with
    | FNeg phi1 ->
      impl_free_cps phi1 (fun (con: formula_wi) -> k (FNeg_wi con))
    | FOr (phi1, phi2) ->
      impl_free_cps phi1
        (fun (con1: formula_wi) ->
           impl_free_cps phi2
             (fun (con11: formula_wi) -> k (FOr_wi (con1, con11))))
    | FAnd (phi1, phi2) ->
      impl_free_cps phi1
        (fun (con2: formula_wi) ->
           impl_free_cps phi2
             (fun (con12: formula_wi) -> k (FAnd_wi (con2, con12))))
    | FImpl (phi1, phi2) ->
      impl_free_cps phi1
        (fun (con3: formula_wi) ->
           impl_free_cps phi2
             (fun (con13: formula_wi) -> k (FOr_wi ((FNeg_wi con3), con13))))
    | FConst phi1 -> k (FConst_wi phi1)
    | FVar phi1 -> k (FVar_wi phi1)
    end

let impl_free_main (phi: formula) : formula_wi =
  impl_free_cps phi (fun (x: formula_wi) -> x)

let rec nnfc_cps : type a . formula_wi -> (formula_wi -> a) ->  a =
  fun phi k -> 
    begin match phi with
    | FNeg_wi FNeg_wi phi1 ->
      nnfc_cps phi1 (fun (con4: formula_wi) -> k con4)
    | FNeg_wi FAnd_wi (phi1, phi2) ->
      nnfc_cps (FNeg_wi phi1)
        (fun (con5: formula_wi) ->
           nnfc_cps (FNeg_wi phi2)
             (fun (con14: formula_wi) -> k (FOr_wi (con5, con14))))
    | FNeg_wi FOr_wi (phi1, phi2) ->
      nnfc_cps (FNeg_wi phi1)
        (fun (con6: formula_wi) ->
           nnfc_cps (FNeg_wi phi2)
             (fun (con15: formula_wi) -> k (FAnd_wi (con6, con15))))
    | FOr_wi (phi1, phi2) ->
      nnfc_cps phi1
        (fun (con7: formula_wi) ->
           nnfc_cps phi2
             (fun (con16: formula_wi) -> k (FOr_wi (con7, con16))))
    | FAnd_wi (phi1, phi2) ->
      nnfc_cps phi1
        (fun (con8: formula_wi) ->
           nnfc_cps phi2
             (fun (con17: formula_wi) -> k (FAnd_wi (con8, con17))))
    | phi1 -> k phi1
    end

let nnfc_main (phi: formula_wi) : formula_wi =
  nnfc_cps phi (fun (x1: formula_wi) -> x1)

let rec distr_cps :
  type a . formula_wi -> formula_wi -> (formula_wi -> a) ->  a =
  fun phi1 phi2 k -> 
    begin match (phi1, phi2) with
    | (FAnd_wi (phi11, phi12), phi21) ->
      distr_cps phi11 phi21
        (fun (con9: formula_wi) ->
           distr_cps phi12 phi21
             (fun (con18: formula_wi) -> k (FAnd_wi (con9, con18))))
    | (phi11, FAnd_wi (phi21, phi22)) ->
      distr_cps phi11 phi21
        (fun (con10: formula_wi) ->
           distr_cps phi11 phi22
             (fun (con19: formula_wi) -> k (FAnd_wi (con10, con19))))
    | (phi11, phi21) -> k (FOr_wi (phi11, phi21))
    end

let distr_main (phi1: formula_wi) (phi2: formula_wi) : formula_wi =
  distr_cps phi1 phi2 (fun (x2: formula_wi) -> x2)

let rec cnfc_cps : type a . formula_wi -> (formula_wi -> a) ->  a =
  fun phi k -> 
    begin match phi with
    | FOr_wi (phi1, phi2) ->
      cnfc_cps phi1
        (fun (con20: formula_wi) ->
           cnfc_cps phi2
             (fun (con110: formula_wi) -> distr_cps con20 con110 k))
    | FAnd_wi (phi1, phi2) ->
      cnfc_cps phi1
        (fun (con21: formula_wi) ->
           cnfc_cps phi2
             (fun (con111: formula_wi) -> k (FAnd_wi (con21, con111))))
    | phi1 -> k phi1
    end

let cnfc_main (phi: formula_wi) : formula_wi =
  cnfc_cps phi (fun (x3: formula_wi) -> x3)

type valuation = ident -> (bool)

let rec eval (v: ident -> (bool)) (f: formula) : bool =
  begin match f with
  | FVar x4 -> v x4
  | FConst b -> b
  | FAnd (f1, f2) -> (eval v f1) && (eval v f2)
  | FOr (f1, f2) -> (eval v f1) || (eval v f2)
  | FImpl (f1, f2) -> (not (eval v f1)) || (eval v f2)
  | FNeg f1 -> not (eval v f1)
  end

let rec eval_wi (v: ident -> (bool)) (f: formula_wi) : bool =
  begin match f with
  | FVar_wi x4 -> v x4
  | FConst_wi b -> b
  | FAnd_wi (f1, f2) -> (eval_wi v f1) && (eval_wi v f2)
  | FOr_wi (f1, f2) -> (eval_wi v f1) || (eval_wi v f2)
  | FNeg_wi f1 -> not (eval_wi v f1)
  end

let rec eval_cps (v: ident -> (bool)) (f: formula) (k: (bool) -> (bool)) :
  bool =
  begin match f with
  | FVar x4 -> k (v x4)
  | FConst b -> k b
  | FAnd (f1, f2) ->
    eval_cps v f1
      (fun (con22: bool) ->
         eval_cps v f2 (fun (con112: bool) -> k (con22 && con112)))
  | FOr (f1, f2) ->
    eval_cps v f1
      (fun (con23: bool) ->
         eval_cps v f2 (fun (con113: bool) -> k (con23 || con113)))
  | FImpl (f1, f2) ->
    eval_cps v f1
      (fun (con24: bool) ->
         eval_cps v f2 (fun (con114: bool) -> k ((not con24) || con114)))
  | FNeg f1 -> eval_cps v f1 (fun (con25: bool) -> k (not con25))
  end

let rec eval_wi_cps (v: ident -> (bool)) (f: formula_wi)
                    (k: (bool) -> (bool)) : bool =
  begin match f with
  | FVar_wi x4 -> k (v x4)
  | FConst_wi b -> k b
  | FAnd_wi (f1, f2) ->
    eval_wi_cps v f1
      (fun (con26: bool) ->
         eval_wi_cps v f2 (fun (con115: bool) -> k (con26 && con115)))
  | FOr_wi (f1, f2) ->
    eval_wi_cps v f1
      (fun (con27: bool) ->
         eval_wi_cps v f2 (fun (con116: bool) -> k (con27 || con116)))
  | FNeg_wi f1 -> eval_wi_cps v f1 (fun (con28: bool) -> k (not con28))
  end

