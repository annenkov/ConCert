From Coq Require Import PeanoNat ZArith Notations Bool.

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.

From ConCert Require Import MyEnv.
From ConCert.Embedding Require Import Notations.
From ConCert.Execution Require Import Blockchain.
From ConCert.Extraction Require Import LiquidityExtract LPretty
     PreludeExt Common CertifyingEta Optimize OptimizeCorrectness.

From Coq Require Import List Ascii String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import All.

Import ListNotations.
Import MonadNotation.

Open Scope Z.

Import Lia.

Definition PREFIX := "coq_".

Module Counter.


  Notation address := nat.

  Definition operation := unit.
  Definition storage := Z × address.

  Definition init (ctx : SimpleCallCtx) (setup : Z * address) : option storage :=
    let ctx' := ctx in (* prevents optimisations from removing unused [ctx]  *)
    Some setup.

  Inductive msg :=
  | Inc (_ : Z)
  | Dec (_ : Z).

  Definition inc_balance (st :  Z × nat) (new_balance : Z)
               (p : (0 <=? new_balance) = true) :=
    (st.1 + new_balance, st.2).


  Definition dec_balance (st : storage) (new_balance : Z)
             (p : (0 <=? new_balance) = true) :=
    (st.1 -  new_balance, st.2).

  Definition my_bool_dec := Eval compute in bool_dec.

  Definition counter (msg : msg) (st : storage)
    : option (list operation * storage) :=
    match msg with
    | Inc i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h =>
        Some ([], inc_balance st i h)
      | right _ => None
      end
    | Dec i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h => Some ([], dec_balance st i h)
      | right _ => None
      end
    end.

  Definition counter_partially_applied (msg : msg) (st : storage)
    : option (list operation * storage) :=
  match msg with
    | Inc i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h =>
        let f := inc_balance st i in
        Some ([], f h)
      | right _ => None
      end
    | Dec i =>
      match (my_bool_dec (0 <=? i) true) with
      | left h => Some ([], dec_balance st i h)
      | right _ => None
      end
    end.


End Counter.

Import Counter.

(** A translation table for definitions we want to remap. The corresponding top-level definitions will be *ignored* *)
Definition TT_remap : list (kername * string) :=
  [ remap <% bool %> "bool"
  ; remap <% list %> "list"
  ; remap <% Amount %> "tez"
  ; remap <% address_coq %> "address"
  ; remap <% time_coq %> "timestamp"
  ; remap <% option %> "option"
  ; remap <% Z.add %> "addInt"
  ; remap <% Z.sub %> "subInt"
  ; remap <% Z.leb %> "leInt"
  ; remap <% Z %> "int"
  ; remap <% nat %> "key_hash" (* type of account addresses*)
  ; remap <% operation %> "operation"
  ; remap <% @fst %> "fst"
  ; remap <% @snd %> "snd" ].

(** A translation table of constructors and some constants. The corresponding definitions will be extracted and renamed. *)
Definition TT_rename : list (string * string):=
  [ ("Some", "Some")
  ; ("None", "None")
  ; ("Z0" ,"0")
  ; ("nil", "[]")
  ; ("true", "true")
  ; (string_of_kername <%% storage %%>, "storage")  (* we add [storage] so it is printed without the prefix *) ].

Definition COUNTER_MODULE : LiquidityMod msg _ (Z × address) storage operation :=
  {| (* a name for the definition with the extracted code *)
     lmd_module_name := "liquidity_counter" ;

     (* definitions of operations on pairs and ints *)
     lmd_prelude := prod_ops ++ nl ++ int_ops;

     (* initial storage *)
     lmd_init := init ;

     (* no extra operations in [init] are required *)
     lmd_init_prelude := "" ;

     (* the main functionality *)
     lmd_receive := counter ;

     (* code for the entry point *)
     lmd_entry_point := printWrapper (PREFIX ++ "counter") ++ nl
                       ++ printMain |}.

Definition quote_recursively_body {A : Type} (def : A) :TemplateMonad program :=
  p <- tmQuoteRecTransp def false ;;
  kn <- match p.2 with
       | tConst name _ => ret name
       | _ => tmFail ("Expected constant, got "  ++
                       TUtil.string_of_term p.2)
       end;;
  match lookup_env p.1 kn with
  | Some (ConstantDecl cb) =>
    match cb.(cst_body) with
    | Some b => ret (p.1, b)
    | None => tmFail ("The constant doesn't have a body: " ++ kn.2)
    end
  | _ => tmFail ("Not found: " ++ kn.2)
  end.

Definition anchor := fun x : nat => x.

Definition CURRENT_MODULE := Eval compute in <%% anchor %%>.1.

MetaCoq Run (counter_syn <- quote_recursively_body counter_partially_applied ;;
             tmDefinition "counter_partially_applied_syn" counter_syn;;
             Σexpanded <- eta_global_env_template
               false
               CURRENT_MODULE
               counter_syn.1
               [<%% inc_balance %%>; <%% counter_partially_applied %%>]
               (fun kn => negb (eq_kername kn <%% inc_balance %%>) &&
                       negb (eq_kername kn <%% counter_partially_applied %%>))
               (fun kn => negb (eq_kername kn <%% inc_balance %%>) &&
                       negb (eq_kername kn <%% counter_partially_applied %%>));;
             tmDefinition "Σexpanded" Σexpanded
            ).

Fixpoint update_global_env (Σ : global_env) (Σup : global_env) : global_env :=
  match Σ with
  | (kn, gd) :: Σ' => match lookup_env Σup kn with
                    | Some v => (kn,v) :: update_global_env Σ' Σup
                    | None => (kn, gd) :: update_global_env Σ' Σup
                    end
  | [] => []
  end.

MetaCoq Run (Σe <- template_of_result (general_specialize_erase_debox_template_env
                    counter_partially_applied_syn.1
                    [<%% inc_balance %%>; <%% counter_partially_applied %%>]
                    (fun kn => negb (eq_kername kn <%% inc_balance %%>) &&
                            negb (eq_kername kn <%% counter_partially_applied %%>))
                    false false);;
             tmDefinition "Σe" Σe ;;
             let ds := analyze_env Σe in
             let ds := trim_dearg_set ds in
             tmDefinition "dearg_set_counter" ds ;;
             match ExAst.lookup_env Σe <%% counter_partially_applied %%> with
             | Some (ExAst.ConstantDecl cb) =>
               match cb.(ExAst.cst_body) with
               | Some b => tmDefinition "counter_papp_erased" b
               | None => tmFail "A constant without a body"
               end
             | _ => tmFail "Something's wrong"
             end;;
             tmPrint "Done").

MetaCoq Run (Σe <- template_of_result (general_specialize_erase_debox_template_env
                    (update_global_env counter_partially_applied_syn.1 Σexpanded)
                    [<%% inc_balance %%>; <%% counter_partially_applied %%>]
                    (fun kn => negb (eq_kername kn <%% inc_balance %%>) &&
                            negb (eq_kername kn <%% counter_partially_applied %%>))
                    false false);;
             match ExAst.lookup_env Σe <%% counter_partially_applied %%> with
             | Some (ExAst.ConstantDecl cb) =>
               match cb.(ExAst.cst_body) with
               | Some b => tmDefinition "counter_papp_erased_expanded" b
               | None => tmFail "A constant without a body"
               end
             | _ => tmFail "Something's wrong"
             end;;
             tmPrint "Done").

Example partially_applied :
  is_expanded dearg_set_counter.(Optimize.ind_masks) dearg_set_counter.(Optimize.const_masks) counter_papp_erased = false.
Proof. reflexivity. Qed.

Example expanded_counter :
  is_expanded dearg_set_counter.(Optimize.ind_masks) dearg_set_counter.(Optimize.const_masks) counter_papp_erased_expanded = true.
Proof. reflexivity. Qed.

(** We run the extraction procedure inside the [TemplateMonad].
    It uses the certified erasure from [MetaCoq] and the certified deboxing procedure
    that removes application of boxes to constants and constructors. *)

Time MetaCoq Run
     (t <- liquitidy_extraction PREFIX TT_remap TT_rename COUNTER_MODULE ;;
      tmDefinition COUNTER_MODULE.(lmd_module_name) t
     ).

Print liquidity_counter.

(** We redirect the extraction result for later processing and compiling with the Liquidity compiler *)
Redirect "./extraction/examples/liquidity-extract/CounterDepCertifiedExtraction.liq" Compute liquidity_counter.
