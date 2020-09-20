From Coq Require Import List PeanoNat Bool String.
From MetaCoq Require Import Template.All.
From ConCert.Extraction Require Import Erasure Optimize Common ResultMonad.
Open Scope nat.

Import Template.Ast.
Import ListNotations.
Import MonadNotation.

Section Eta.
  Definition ctors_info := list (inductive * nat * nat * term).
  Definition constansts_info := list (kername * nat * term).
  Context (ctors : ctors_info).

  Context (constants : constansts_info).

  Fixpoint remove_top_prod (t : Ast.term) (n : nat) :=
    match n,t with
    | O, _  => t
    | S m, tProd nm ty1 ty2 => remove_top_prod ty2 m
    | _, _ => t
    end.

  Definition eta_single (t : Ast.term) (args : list Ast.term) (ty : Ast.term) (count : nat): term :=
    let needed := count - #|args| in
    let prev_args := map (lift0 needed) args in
    let eta_args := rev_map tRel (seq 0 needed) in
    let cut_ty := remove_top_prod ty #|args| in
    (* NOTE: we substitute the arguments in order to "specialise" types according to the application *)
    (* TODO: handle recursive inductives (requires subsitusion of the inductive itself)*)
    let subst_ty := subst (rev args) 0 cut_ty in
    let remaining := firstn needed (decompose_prod subst_ty).1.2 in
    let remaining_names := firstn needed (decompose_prod subst_ty).1.1 in
    fold_right (fun '(nm,ty) b => Ast.tLambda nm ty b) (mkApps t (prev_args ++ eta_args)) (combine remaining_names remaining).

  Definition eta_ctor (ind : inductive) (c : nat)
           (u : Instance.t)
           (args : list term) : term :=
    match find (fun '(ind', c', _, _) => eq_inductive ind' ind && (c' =? c)) ctors with
  | Some (_, _,n,ty) => eta_single (Ast.tConstruct ind c u) args ty n
  | None => mkApps (tConstruct ind c u) args
    end.

Definition eta_const (kn : kername) (u : Instance.t) (args : list term) : term :=
  match find (fun '(kn',n, _) => eq_kername kn' kn) constants with
  | Some (_, n, ty) => eta_single (tConst kn u) args ty n
  | None => mkApps (tConst kn u) args
  end.

(** We assume that all applications are "flattened" e.g. of the form
    [tApp hd [t1; t2; t3; ...; tn]] where hd itself is not an application.
    This is guaranteed for quoted terms. *)
Fixpoint eta_expand (t : term) : term :=
  match t with
  | tApp hd args =>
    match hd with
      | tConstruct ind c u => eta_ctor ind c u (map eta_expand args)
      | tConst kn u => eta_const kn u (map eta_expand args)
      | _ => mkApps (eta_expand hd) (map eta_expand args)
    end
  | tEvar n ts => tEvar n (map eta_expand ts)
  | tLambda na ty body => tLambda na ty (eta_expand body)
  | tLetIn na val ty body => tLetIn na (eta_expand val) ty (eta_expand body)
  | tCase p ty disc brs =>
    tCase p ty (eta_expand disc) (map (on_snd eta_expand) brs)
  | tProj p t => tProj p (eta_expand t)
  | tFix def i => tFix (map (map_def id eta_expand) def) i
  | tCoFix def i => tCoFix (map (map_def id eta_expand) def) i
  (* NOTE: we know that constructros and constants are not applied at this point,
     since applications are captured by the previous cases *)
  | tConstruct ind c u => eta_ctor ind c u (map eta_expand [])
  | tConst kn u => eta_const kn u (map eta_expand [])
  | t => t
  end.

End Eta.

Definition from_oib (ds : dearg_set) (kn : kername) (ind_index : nat) (oib : one_inductive_body) : ctors_info :=
  let f i '(_, ty, c) :=
      let ind := mkInd kn ind_index in
      let mm := get_mib_masks ds.(ind_masks) kn in
      match mm with
      | Some m =>
        let cm := get_ctor_mask ds.(ind_masks) ind i in
        Some (ind,i,#|cm|,ty)
      | None => None
      end in
  fold_lefti (fun i acc c => match f i c with Some v => v :: acc| None => acc end)
             0  oib.(ind_ctors) [].

Fixpoint get_eta_info (Σ : global_env) (ds : dearg_set) : ctors_info * constansts_info :=
  match Σ with
  | (kn, InductiveDecl mib) :: Σ' =>
    let '(ctors, consts) := get_eta_info Σ' ds in
    (List.concat (mapi (from_oib ds kn) mib.(ind_bodies)) ++ ctors, consts)%list
  | (kn, ConstantDecl cb) :: Σ' =>
    let '(ctors, consts) := get_eta_info Σ' ds in
    (ctors, (kn, #|get_const_mask ds.(const_masks) kn|, cb.(cst_type)) :: consts)
  | [] => ([],[])
  end.


Definition ds_ (full_eta : bool) (p : program) : result _ string :=
  let Σ := p.1 in
  entry <- match p.2 with
          | tConst kn _ => ret kn
          | tInd ind _ => ret (inductive_mind ind)
          | _ => Err "Expected program to be a tConst or tInd"
          end;;
  Σe <- specialize_erase_template_env_no_wf_check Σ [entry] [];;
  let ds := analyze_env Σe in
  if full_eta then ret ds else ret (trim_dearg_set ds).

Definition eta_info_ (full_eta : bool) (p : program) : result _ string :=
  let Σ := p.1 in
  entry <- match p.2 with
          | tConst kn _ => ret kn
          | tInd ind _ => ret (inductive_mind ind)
          | _ => Err "Expected program to be a tConst or tInd"
          end;;
  Σe <- specialize_erase_template_env_no_wf_check Σ [entry] [];;
  let ds := analyze_env Σe in
  let ds := if full_eta then ds else trim_dearg_set ds in
  ret (get_eta_info p.1 ds).

Definition template_of_result {A} (res : result A string) : TemplateMonad A :=
  t <- tmEval lazy res ;;
  match t with
  | Ok v => ret v
  | Err e => tmFail e
  end.

Definition eta_prog (full_eta : bool)(p : program) : result term string :=
  let Σ := p.1 in
  entry <- match p.2 with
          | tConst kn _ => ret kn
          | tInd ind _ => ret (inductive_mind ind)
          | _ => Err "Expected program to be a tConst or tInd"
          end;;
  Σe <- specialize_erase_template_env_no_wf_check Σ [entry] [];;
  let ds := analyze_env Σe in
  let ds' := if full_eta then ds else trim_dearg_set ds in
  b <- result_of_option (lookup_env Σ entry) "No item" ;;
  match b with
  | ConstantDecl cb =>
    t <- result_of_option cb.(cst_body) "No body" ;;
    let (ctors, consts) := get_eta_info Σ ds' in
    ret (eta_expand ctors consts t)
  | _ => Err "Not supported"
  end.

Fixpoint change_modpath (mpath : modpath) (ignore : kername -> bool) (t : term) : term :=
  match t with
  | tRel n => t
  | tVar id => t
  | tSort s => t
  | tEvar ev args => tEvar ev (map (change_modpath mpath ignore) args)
  | tCast t kind v => tCast (change_modpath mpath ignore t) kind (change_modpath mpath ignore v)
  | tProd na ty body => tProd na (change_modpath mpath ignore ty) (change_modpath mpath ignore body)
  | tLambda na ty body => tLambda na (change_modpath mpath ignore ty) (change_modpath mpath ignore body)
  | tLetIn na def def_ty body =>
    tLetIn na (change_modpath mpath ignore def) (change_modpath mpath ignore def_ty) (change_modpath mpath ignore body)
  | tApp f args => tApp (change_modpath mpath ignore f) (map (change_modpath mpath ignore) args)
  | tConst kn u => if ignore kn then t
                  else tConst (mpath, kn.2 ++ "_expanded") u
  | tInd ind u => t
  | tConstruct ind idx u => t
  | tCase ind_and_nbparams type_info discr branches =>
    tCase ind_and_nbparams (change_modpath mpath ignore type_info)
          (change_modpath mpath ignore discr) (map (on_snd (change_modpath mpath ignore)) branches)
  | tProj proj t => tProj proj (change_modpath mpath ignore t)
  | tFix mfix idx => tFix (map (map_def (change_modpath mpath ignore) (change_modpath mpath ignore)) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def (change_modpath mpath ignore) (change_modpath mpath ignore)) mfix) idx
  end.

Definition generate_proof (Σ1 Σ2 : global_env) (kn1 kn2 : kername) : TemplateMonad (term × term × term × term) :=
  match lookup_env Σ1 kn1, lookup_env Σ2 kn2  with
  | Some (ConstantDecl cb1), Some (ConstantDecl cb2) =>
    match cb1.(cst_body), cb2.(cst_body) with
    | Some _, Some exp_body =>
      let ty := cb1.(cst_type) in
      let proof_ty :=
          tApp (tInd
                  {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
                     inductive_ind := 0 |} [])
               [ty; tConst kn1 []; tConst kn2 []] in
      let proof_body := tApp (tConstruct
                          {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
                             inductive_ind := 0 |} 0 [])
                       [ty;tConst kn1 []] in
      ret (cb1.(cst_type), (exp_body, (proof_ty, proof_body)))
    | _,_ => tmFail "No body"
    end
  | None, _ => tmFail ("Not found: " ++ kn1.2)
  | _, None => tmFail ("Not found: " ++ kn2.2)
  | _,_ => tmFail "Not a constant"
  end.

Definition gen_proof_prog (Σ1 Σ2 : global_env) (kn1 kn2 : kername) : TemplateMonad unit :=
  '(exp_ty, (exp_t, (p_ty, p_t))) <- generate_proof Σ1 Σ2 kn1 kn2 ;;
  tmBind (tmUnquoteTyped Type exp_ty)
         (fun A => ucst <- tmUnquoteTyped A exp_t ;;
                 tmDefinition kn2.2 ucst;;
            tmBind (tmUnquoteTyped Type p_ty)
                   (fun B =>
                      uproof <- tmUnquoteTyped B p_t ;;
                      tmDefinition (kn2.2++"_correct") uproof ;;
                      tmPrint B)).

Definition contains_global_env (Σ : global_env) (kn : kername) :=
  match lookup_env Σ kn with
  | Some v => true
  | None => false
  end.

Definition restrict_env (Σ : global_env) (kns : list kername) : global_env :=
  filter (fun '(kn, _) => match find (eq_kername kn) kns with
                       |Some _ => true
                       | None => false
                       end) Σ.

Fixpoint map_constants_global_env (k : kername -> kername) (f : constant_body -> constant_body) (Σ : global_env) : global_env :=
  match Σ with
  | [] => []
  | (kn, ConstantDecl cb) :: Σ' => (k kn, ConstantDecl (f cb)) :: map_constants_global_env k f Σ'
  | gd :: Σ' => gd :: map_constants_global_env k f Σ'
  end.

Definition add_suffix_global_env (mpath : modpath) (ignore : kername -> bool) (Σ : global_env) :=
  map_constants_global_env
    (fun kn => (mpath,kn.2 ++ "_expanded"))
    (fun cb => {| cst_type := cb.(cst_type);
               cst_body := b <- cb.(cst_body);;
                           Some (change_modpath mpath ignore b);
                cst_universes := cb.(cst_universes) |}) Σ.

Definition eta_global_env (full_eta : bool)(Σ : global_env) (seeds : list kername) (ignore : kername -> bool) :
  result _ string :=
  Σe <- general_specialize_erase_debox_template_env Σ seeds ignore false false;;
  let ds := analyze_env Σe in
  let ds' := if full_eta then ds else trim_dearg_set ds in
  let f cb :=
      match cb.(cst_body) with
      | Some b => let (ctors, consts) := get_eta_info Σ ds' in
                 {| cst_type := cb.(cst_type);
                    cst_body := Some (eta_expand ctors consts b);
                    cst_universes := cb.(cst_universes) |}
      | None => cb
      end in
  let Σ' := restrict_env Σ (map fst Σe) in
  ret (map_constants_global_env id f Σ').

Definition is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition gen_expanded_const_and_proof (Σ : global_env) (mpath : modpath) (ignore : kername -> bool)  : TemplateMonad unit :=
  let Σdecls := filter (fun '(kn,gd) => match gd with
                                    | ConstantDecl cb => negb (is_none cb.(cst_body))
                                    | _ => false
                                     end) Σ in
  Σdecls' <- tmEval lazy (add_suffix_global_env mpath ignore Σdecls) ;;
  monad_iter (fun kn1 => gen_proof_prog Σ Σdecls' kn1 (mpath,kn1.2 ++ "_expanded"))
             (List.rev (map fst Σdecls)).

Definition eta_global_env_template (full_eta : bool) (mpath : modpath) (Σ : global_env) (seeds : list kername) (ignore : kername -> bool) (cst_name_ignore : kername -> bool) : TemplateMonad global_env :=
  Σext <- template_of_result (eta_global_env full_eta Σ seeds ignore) ;;
  gen_expanded_const_and_proof Σext mpath cst_name_ignore;;
  ret Σext.

Definition eta_expand_def {A} (full_eta : bool) (mpath : modpath) (cst_name_ignore : kername -> bool) (def : A) : TemplateMonad _ :=
  p <- tmQuoteRecTransp def false ;;
  kn <- extract_def_name def ;;
  eta_global_env_template full_eta mpath p.1 [kn] (fun _ => false) cst_name_ignore .

Module Ex1.
Definition partial_app_pair :=
  let p : forall B : Type, unit -> B -> unit × B:= @pair unit in
  p bool tt true.
End Ex1.
MetaCoq Quote Recursively Definition p_app_pair_syn := Ex1.partial_app_pair.

Definition anchor := fun x : nat => x.
Definition CURRENT_MODULE := Eval compute in <%% anchor %%>.1.

Definition modpath_eq_dec (mp1 mp2 : modpath) : {mp1 = mp2} + {mp1 <> mp2}.
  repeat decide equality.
Defined.

Definition eq_modpath (mp1 mp2 : modpath) : bool :=
  match modpath_eq_dec mp1 mp2 with
  | left _ => true
  | right _ => false
  end.

Definition only_from_module_of (kn_base : kername) :=
  fun (kn : kername) => negb (eq_modpath kn_base.1 kn.1).

Module Test1.
  Definition anchor := fun x : nat => x.
  Definition CURRENT_MODULE := Eval compute in <%% anchor %%>.1.
  MetaCoq Run (eta_global_env_template
                 true CURRENT_MODULE
                 p_app_pair_syn.1
                 [<%% Ex1.partial_app_pair %%>]
                 (fun _ => false)
                 (fun _ => false)).
End Test1.


Inductive MyInd (A B C : Type) :=
  miCtor : A * A -> B -> C -> True -> MyInd A B C.

Module Ex2.
  Definition partial_app1 A B n m := let f := miCtor A in f B bool (let n' := @pair A in n' A n n) m true I.
  Definition partial_app2 := let f := partial_app1 in f bool true.
End Ex2.

Set Printing Implicit.
(** Expands the dependencies and adds the corresponding definitions *)
MetaCoq Run (eta_expand_def
               false
               CURRENT_MODULE
               (only_from_module_of <%% Ex2.partial_app2 %%>)
               Ex2.partial_app2).

(** [partial_app2_expanded] is defined in terms of [partial_app1_expanded] *)
Print partial_app2_expanded.
(* partial_app2_expanded =
let f := fun H H0 : Type => partial_app1_expanded H H0 in f bool true
     : bool -> true -> MyInd bool true bool
 *)

Inductive MyInd1 (A B C : Type) :=
  | miCtor0 : MyInd1 A B C
  | miCtor1 : A * A -> B -> True -> C -> MyInd1 A B C.

Definition partial_app3 A B n m :=
  let f := miCtor1 A in f B bool n m I.

MetaCoq Run (eta_expand_def
               false
               CURRENT_MODULE
               (only_from_module_of <%% partial_app3 %%>)
               partial_app3).

Module Ex3.
Definition inc_balance (st :  nat × nat) (new_balance : nat)
               (p : (0 <=? new_balance) = true) :=
  (st.1 + new_balance, st.2).

Definition partial_inc_balance st i := inc_balance st i.
End Ex3.
MetaCoq Run (p <- tmQuoteRecTransp Ex3.partial_inc_balance false ;;
             eta_global_env_template
               false
               CURRENT_MODULE
               p.1
               [<%% Ex3.inc_balance %%>; <%% Ex3.partial_inc_balance %%>]
               (fun _ => false)
               (only_from_module_of <%% Ex3.partial_inc_balance %%>)
            ).
