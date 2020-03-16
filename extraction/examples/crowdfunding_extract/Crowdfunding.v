(**  We develop a deep embedding of a crowdfunding contract and prove some of its functional correctness properties using the corresponding shallow embedding *)

Require Import String ZArith Basics.
From ConCert.Embedding Require Import Ast Notations CustomTactics
     PCUICTranslate PCUICtoTemplate Utils MyEnv.

From ConCert.Extraction Require Import Liquidity.
From ConCert.Extraction.Examples Require Import Prelude CrowdfundingData SimpleBlockchain.

Require Import List PeanoNat ssrbool.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Open Scope list.

Import Lia.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)


(** * The crowdfunding contract *)

Module CrowdfundingContract.

  Import AcornBlockchain.

  (** Generating string constants for variable names *)

  Run TemplateProgram (mkNames ["c";"s";"e";"m";"v";"dl"; "g"; "chain";
                                  "tx_amount"; "bal"; "sender"; "own"; "isdone" ;
                                    "accs"; "now"; "newstate"; "newmap"; "cond" ] "").


  (** ** AST of the [init] function *)
  Module Init.
    Import Notations.
    Definition crowdfunding_init : expr :=
      [| \own : address => \dl : time => \g : money =>
         mkFullState (mkParams dl g own) (mkState MNil False) |].

    Make Definition init :=
      (expr_to_tc Σ' (indexify nil crowdfunding_init)).

    Check init.
 End Init.

 (** ** AST of the [receive] function *)
 Module Receive.

   Import CrowdfundingData.Notations.
     (** Constructors. [Res] is an abbreviation for [Some (st, [action]) : option (State * list ActionBody)] *)

  Definition actions_ty := [! "list" "SimpleActionBody" !].

  Notation "'Result'" := [!"prod"  ("list" "SimpleActionBody") {full_state_ty} !]
                           (in custom type at level 2).

  Notation "'Transfer' a b" :=
    [| {eConstr SActionBody "Act_transfer"} {b} {a} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  Definition eqb_addr (a1 a2 : address_coq) :=
    match a1, a2 with
    | ContractAddr_coq n1, ContractAddr_coq n2 => Nat.eqb n1 n2
    | UserAddr_coq n1, UserAddr_coq n2 => Nat.eqb n1 n2
    | _, _ => false
    end.

  Notation "a ==a b" := [| {eConst "eqb_addr"} {a} {b} |]
                        (in custom expr at level 0).


   (** We specialise some polymorphic constructors to avoid writing types all the time *)
   Notation "'#Just' a" := [| $Just$Maybe  [: Result ] {a}|]
                           (in custom expr at level 0,
                               a custom expr at level 1).

   Notation "'#Pair' a b" := [| $"pair"$"prod" [: {actions_ty}] [: {full_state_ty}] {a} {b} |]
                           (in custom expr at level 0,
                               a custom expr at level 1,
                               b custom expr at level 1).

   Notation "'#Nothing'" := (eApp (eConstr "option" "None") (eTy [!Result!]))
                              (in custom expr at level 0).

   Notation "'#Nil'" := [| {eConstr "list" "nil"} {eTy (tyInd SActionBody)} |]
                      (in custom expr at level 0).
   Notation "[ x ]" := [| {eConstr "list" "cons"} {eTy (tyInd SActionBody)} {x} #Nil |]
                        ( in custom expr at level 0,
                          x custom expr at level 1).



   Notation "'DONE'" := (eConst "set_done")
                          (in custom expr at level 0).
   Notation "'UPDATE_CONTRIBS'" := (eConst "update_contribs")
                                    (in custom expr at level 0).

   Definition lookup k m := lookup_map m k.

   Notation "'findm' a b" :=  [| {eConst "lookup"} {a} {b} |]
        (in custom expr at level 0,
            a custom expr at level 1,
            b custom expr at level 1).

   Notation SCtx := "SimpleContractCallContext".
   Notation SChain := "SimpleChain".

   Definition maybe_bind_syn :=
     [| \\"A" => \\"B" => \"o" : Maybe '"A" => \"f" : '"A" -> Maybe '"B" =>
        case "o" : Maybe '"A" return Maybe '"B" of
        | Just "x" -> "f" "x"
        | Nothing -> $Nothing$Maybe [: '"B" ]  |].

   Make Definition maybe_bind :=
     (expr_to_tc Σ' (indexify nil maybe_bind_syn)).

   Notation "a >>= b : A , B" :=
     [| {eConst "maybe_bind"} A B a b |]
       (in custom expr at level 0,
           A custom type,
           B custom type,
           a custom expr,
           b custom expr).

   Notation "a >> b : A , B" :=
     [| {eConst "maybe_bind"} [: {A} ] [: {B} ] {a} (\"x" : {A} => {b})|]
       (in custom expr at level 0,
           A custom type at level 1,
           B custom type at level 1,
           a custom expr,
           b custom expr).

   Definition validate_syn :=
     [| \tx_amount : money =>
        if 0z < tx_amount then $Just$Maybe [: Unit] star
        else $Nothing$Maybe [: Unit] : Maybe Unit |].

   Make Definition validate :=
     (expr_to_tc Σ' (indexify nil validate_syn)).


   Notation "'VALIDATE' amt" := [| {eConst "validate"} {amt} |] (in custom expr at level 0).

   Definition crowdfunding : expr :=
     [| \sender : address => \bal : money => \tx_amount : money =>
        \now : time => \m : msg => \s : {full_state_ty} =>
         let own : address := owner s in
         let accs : Map := contribs s in
         case m : msg return Maybe Result of
            | GetFunds ->
              if (own ==a sender) && (deadline s <t now) && (goal s <= bal) then
                (VALIDATE tx_amount) >> (#Just (#Pair [Transfer bal sender] (DONE s))) : Unit, Result
             else #Nothing : Maybe Result
            | Donate ->
              if now <=t deadline s then
                (case (findm sender accs) : Maybe money return Maybe Result of
                  | Just v ->
                    let newmap : Map := madd sender (v + tx_amount) accs in
                    #Just (#Pair #Nil (UPDATE_CONTRIBS s newmap))
                  | Nothing ->
                    let newmap : Map := madd sender tx_amount accs in
                    #Just (#Pair #Nil (UPDATE_CONTRIBS s newmap)))
              else #Nothing : Maybe Result
           | Claim ->
             if (deadline s <t now) && (bal < goal s) && (~ done s) then
             (case (findm sender accs) : Maybe money return Maybe Result of
              | Just v -> let newmap : Map := madd sender 0z accs in
                 #Just (#Pair [Transfer v sender] (UPDATE_CONTRIBS s newmap))
              | Nothing -> #Nothing)
             else #Nothing : Maybe Result
    |].

  Make Definition receive :=
    (expr_to_tc Σ' (indexify nil crowdfunding)).

  Eval simpl in receive.

  End Receive.
End CrowdfundingContract.

Import CrowdfundingContract.

(** Packing together the data type definitions and functions *)
Definition CFModule : LiquidityModule :=
  {| datatypes := [msg_syn];
     storage := [! {full_state_ty} !];
     message := [! msg !];
     init := Init.crowdfunding_init;
     functions := [("update_contribs", update_contribs_syn);
                     ("set_done", set_done_syn);
                     ("receive", Receive.crowdfunding)
                  ];
     main := "receive";
     main_extra_args:=
       ["(Current.sender ())";
          "(Current.balance ())";
          "(Current.amount ())";
          "(Current.time())"] |}.


(** A translation table for types *)
Definition TTty : env string :=
  [("Coq.Numbers.BinNums.Z", "tez");
     ("time_coq", "timestamp");
     ("address_coq", "address");
     ("addr_map", "(address,tez) map");
     ("Coq.Init.Datatypes.nat", "nat")].

(** A translation table for primitive binary operations *)
Definition TT : env string :=
  [("Coq.ZArith.BinInt.Z.add", "addTez");
     ("PeanoNat.Nat.ltb", "ltbN");
     ("PeanoNat.Nat.leb", "lebN");
     ("PeanoNat.Nat.eqb", "eqN");
     ("Coq.ZArith.BinInt.Z.leb", "lebTez");
     ("Coq.ZArith.BinInt.Z.ltb", "ltbTez");
     ("negb", "not");
     ("add_map", "Map.add");
     ("lookup", "Map.find")].

Compute liquidifyModule TT TTty CFModule.
