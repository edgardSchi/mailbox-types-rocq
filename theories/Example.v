(** * Example *)

From MailboxTypes Require Import TypingRules.
From MailboxTypes Require Import Util.
From MailboxTypes Require Import Substitution.

From Stdlib Require Import Lists.List.
Import ListNotations.


(*
  def client() : 1 {
    let server = new in
    spawn server_listen(server);
    let self = new in
    server!Ping[self];
    guard self : _ {
      receive Pong[r] from self |-> free self; ()
    }
  }

   def server_listen(self) : 1 {
      guard self : Ping {
        receive Ping[reply] from self |->
          reply!Pong[sefl];
          free self; ()
      }
   }

  def client() : 1 {
    let server = new in
    let spawn server_listen(server) in
    let self = new in
    let server!Ping[self] in
    guard self : _ {
      receive Pong[r] from self |-> free self; ()
    }
  }
*)

Infix ";;" := TLet (at level 66, left associativity).

(** ** Ping Pong example *)
Section ping_pong_example.

  Inductive PingPong : Type :=
    | Ping
    | Pong.

  Instance PingPongMessage : IMessage PingPong.
  Proof.
    constructor.
    - destruct m, n; now (left + right).
    - apply (fun _ => 1).
  Defined.

  Definition sig (m : PingPong) :=
    match m with
    | Ping => TTMailbox(! « Pong »)
    | Pong => TTBase BTUnit
    end.

  Inductive PingPongDefinition : Type :=
    | Client
    | ServerListen.

  Instance PingPongDefinitionName : IDefinitionName PingPongDefinition.
  Proof.
    constructor; destruct m; destruct n; now (left + right).
  Defined.

  Definition Client_body : Term :=
    TLet
      TNew
      (TLet (TSpawn (TApp ServerListen (ValueVar 0)))
        (TLet TNew
          (TLet (TSend (ValueVar 2) Ping (ValueVar 0))
            (TGuard (ValueVar 1) « Pong » [
                GReceive Pong (TGuard (ValueVar 1) 𝟙 [GFree (TValue ValueUnit)])
              ])
      ))).

  Compute lift 3 4 (ValueVar 3).
  Compute lift 2 1 (TLet (TValue ValueUnit) (TValue (ValueVar 1))).
  Compute subst (ValueUnit) 3 Client_body.
  Compute lift 0 4 Client_body.

  Definition ServerListen_body : Term :=
    TGuard (ValueVar 0) (« Ping » ⊕ 𝟙) [
      GReceive Ping (TLet (TSend (ValueVar 0) Pong (ValueUnit)) (TGuard (ValueVar 2) 𝟙 [GFree (TValue ValueUnit)]));
      GFree (TValue ValueUnit)
    ].

  Definition ClientDefinition : FunctionDefinition :=
    FunDef Client (TUBase BTUnit) (TUBase BTUnit) Client_body.

  (* We use ⋆ « Ping »*)
  Definition ServerListenDefinition : FunctionDefinition :=
    FunDef ServerListen (? « Ping » ⊕ 𝟙 ^^ •) (TUBase BTUnit) ServerListen_body.

  Definition PingPongDefinitions (d : PingPongDefinition) :=
    match d with
    | Client => ClientDefinition
    | ServerListen => ServerListenDefinition
    end.

  Definition PingPongProgram :=
    {|
      signature := sig
    ; definitions := PingPongDefinitions
    ; initialTerm := Client_body
    |}.

  Lemma ServerListen_WellTyped : WellTypedDefinition PingPongProgram ServerListenDefinition.
  Proof.
    constructor.
    unfold ServerListen_body.
    eapply GUARD with (env1 := [Some (? « Ping » ⊕ 𝟙 ^^ •)]) (env2 := [None]) (f := (« Ping » ⊙ 𝟙) ⊕ 𝟙).
    - repeat constructor.
    - eapply SUB with (T1 := (? « Ping » ⊕ 𝟙^^ •)) (env2 := [Some (? « Ping » ⊕ 𝟙 ^^ •)]).
      + apply EnvironmentSubtype_refl.
      + constructor.
        * intros m mIn.
          inversion mIn; subst.
          apply MPValueChoiceLeft.
          now apply MPComp_MPInclusion_One.
          now apply MPValueChoiceRight.
        * constructor.
      + rewrite <- raw_insert_zero.
        repeat constructor.
    - constructor.
      + econstructor.
        * simpl; reflexivity.
        * now right.
        * eapply LET with
            (T1 := TTBase BTUnit)
            (env1 := (insert 0 (! « Pong » ^^ ◦) [None; None]))
            (env2 := (insert 1 (? 𝟙 ^^ •) [None; None])).
          -- repeat rewrite raw_insert_successor.
             repeat rewrite raw_insert_zero.
             simpl.
             rewrite lookup_zero.
             repeat constructor.
          -- simpl.
             eapply SEND with
               (env1 := insert 0 (! « Pong » ^^ ◦) [None ; None])
               (env2 := [None; None ; None]).
             ++ repeat constructor.
             ++ simpl; reflexivity.
             ++ repeat rewrite raw_insert_zero; repeat constructor.
             ++ simpl.
                constructor; repeat constructor.
          -- eapply GUARD with
               (f := 𝟙)
               (env1 := insert 2 (? 𝟙 ^^ •) [None; None; None])
               (env2 := insert 0 (TUBase BTUnit) [None; None; None]).
             ++ repeat rewrite raw_insert_successor.
               repeat rewrite raw_insert_zero.
               simpl.
               repeat rewrite lookup_zero.
               repeat constructor.
             ++ repeat constructor.
             ++ do 2 constructor.
                eapply SUB with (env2 := repeat None 4).
                ** simpl; rewrite raw_insert_zero; repeat constructor.
                ** apply Subtype_refl.
                ** simpl; repeat constructor.
             ++ reflexivity.
             ++ repeat constructor.
      + repeat constructor.
    - intros m mIn.
      inversion mIn; subst.
      apply MPValueChoiceLeft.
      now apply MPComp_MPInclusion_One.
      now apply MPValueChoiceRight.
    - repeat constructor; econstructor.
      + repeat constructor.
      + rewrite MPComp_zero_right.
        rewrite MPChoice_unit.
        rewrite MPChoice_unit.
        now rewrite MPComp_unit.
  Qed.

  Lemma Client_Welltyped : WellTypedDefinition PingPongProgram ClientDefinition.
  Proof.
    constructor.
    unfold Client_body.
    eapply LET with
      (T1 := TTMailbox (? 𝟙))
      (env1 := [Some (TUBase BTUnit)])
      (env2 := [None]).
    - repeat constructor.
    - eapply SUB with (env2 := [None]); repeat constructor; reflexivity.
    - simpl.
      eapply LET with
        (T1 := TTBase BTUnit)
        (env1 := [Some (? (« Ping » ⊕ 𝟙) ⊙ 𝟙 ^^ ◦); None])
        (env2 := [Some (! (« Ping » ⊕ 𝟙) ^^ •); None]).
      + repeat rewrite raw_insert_zero; repeat constructor.
      + apply SPAWN with (env := [Some (? (« Ping » ⊕ 𝟙) ⊙ 𝟙 ^^ •); None]).
        * eapply APP; simpl; try reflexivity.
          eapply SUB with (T1 := ? (« Ping » ⊕ 𝟙) ⊙ 𝟙 ^^ •).
          apply EnvironmentSubtype_refl.
          constructor. intros m mIn. now rewrite MPComp_unit in mIn.
          constructor.
          rewrite <- raw_insert_zero; repeat constructor.
        * reflexivity.
      + simpl.
        eapply LET with
          (T1 := TTMailbox (? 𝟙))
          (env1 := [None; None; None])
          (env2 := insert 0 (TUBase BTUnit) [Some (! « Ping » ⊕ 𝟙 ^^ •); None]).
        * repeat rewrite raw_insert_zero; repeat constructor.
        * apply NEW; repeat constructor.
        * simpl.
          eapply LET with
            (T1 := TTBase BTUnit)
            (env1 := [Some (! « Pong » ^^ ◦); Some (TUBase BTUnit); Some (! « Ping » ⊕ 𝟙 ^^ •); None])
            (env2 := [Some (? « Pong » ⊙ 𝟙 ^^ •); None; None; None]).
          -- repeat rewrite raw_insert_zero; repeat constructor.
          -- eapply SEND with
              (env1 := [None; None; Some (! « Ping » ⊕ 𝟙 ^^ •); None])
              (env2 := [Some (! « Pong » ^^ ◦); Some (TUBase BTUnit); None; None]).
            ++ eapply SUB with (env2 := [None; None; Some (! « Ping » ^^ ◦); None]).
               ** now repeat constructor.
               ** apply Subtype_refl.
               ** replace [None; None; Some (! « Ping » ^^ ◦); None] with (insert 2 (! « Ping » ^^ ◦) [None; None; None])
                  by (repeat rewrite raw_insert_successor; simpl; rewrite lookup_zero; now rewrite raw_insert_zero).
                  repeat constructor.
            ++ simpl; reflexivity.
            ++ repeat constructor.
            ++ simpl.
               eapply SUB with (env2 := [Some (! « Pong » ^^ ◦); None; None; None]).
               ** do 2 constructor; try reflexivity; now repeat constructor.
               ** apply Subtype_refl.
               ** rewrite <- raw_insert_zero; repeat constructor.
          -- eapply SUB with (env2 := [None; Some (? « Pong » ⊙ 𝟙 ^^ •); None; None; None]).
             ++ rewrite raw_insert_zero; repeat constructor; reflexivity.
             ++ apply Subtype_refl.
             ++ eapply GUARD with
                  (env1 := insert 1 (? « Pong » ⊙ 𝟙 ^^ •) [None; None; None; None])
                  (env2 := [None; None; None; None; None]).
               ** rewrite raw_insert_successor; rewrite raw_insert_zero; rewrite lookup_zero; simpl.
                  repeat constructor.
               ** repeat constructor.
               ** apply SINGLE.
                  eapply RECEIVE.
                  --- simpl; reflexivity.
                  --- now left.
                  --- eapply GUARD with
                        (env1 := insert 1 (? 𝟙 ^^ •) [Some (TUBase BTUnit); None; None; None; None; None])
                        (env2 := [None; None; None; None; None; None; None]).
                      +++ rewrite raw_insert_successor.
                          repeat rewrite raw_insert_zero.
                          rewrite lookup_zero; simpl.
                          repeat constructor.
                      +++ eapply SUB with (env2 := insert 1 (? 𝟙 ^^ •) [None; None; None; None; None; None]).
                          repeat rewrite raw_insert_successor;
                          repeat rewrite raw_insert_zero.
                          repeat rewrite lookup_zero; simpl; repeat constructor; reflexivity.
                          apply Subtype_refl.
                          repeat constructor.
                      +++ repeat constructor.
                      +++ reflexivity.
                      +++ repeat constructor.
               ** apply MPComp_MPInclusion_One.
               ** constructor; econstructor.
                  repeat constructor.
                  rewrite MPComp_unit.
                  rewrite MPComp_zero_right.
                  now rewrite MPChoice_unit.
  Qed.

End ping_pong_example.

(** ** Future example *)
(**
  Since our formalization only allows for functions and messages with a single type,
  we can't represents these examples.
  We only show how the types can be defined.
*)
Section future_example.

(** [Future] defines the message atoms *)
Inductive Future : Type :=
  | Put   : Future
  | Get   : Future
  | Reply : Future.

(** We show that [Future] has decidable equality *)
Instance FutureMessage : IMessage Future.
Proof.
  constructor.
  - destruct m; destruct n;
    try (now left);
    try (now right).
  - apply (fun _ => 1).
Defined.

(** Function definition names used in the program *)
Inductive FutureDefinition : Type :=
  | EmptyFutureDef : FutureDefinition
  | FullFutureDef  : FutureDefinition
  | ClientDef      : FutureDefinition.

(** We show that [FutureDefinitionName] has decidable equality *)
Instance FutureDefinitionName : IDefinitionName FutureDefinition.
Proof.
  constructor; destruct m; destruct n;
  try (now left);
  try (now right).
Defined.

(** We define the appropriate types used in the program *)
Definition ClientSendType : @MType Future FutureMessage :=
  ! « Reply ».

Definition ClientReceiveType : @MType Future FutureMessage :=
  ? « Reply ».

Definition EmptyFutureType : @MType Future FutureMessage :=
  ? (« Put » ⊙ (⋆ « Get »)).

Definition FullFutureType : @MType Future FutureMessage :=
  ? ⋆ « Get ».

(** Defining the signature of messages *)
Definition FutureMessageTypes (m : Future) : list TType :=
  match m with
  | Reply => TTBase BTBool :: nil
  | Put   => TTBase BTBool :: nil
  | Get   => TTMailbox (! « Reply ») :: nil
  end.

End future_example.
