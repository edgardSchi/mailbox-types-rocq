(** * Future example *)

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

  M ; N = let x : 1 = M in N = TLet M N
  => M ;; N


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

  (*Definition Client_body : Term :=*)
  (*  TNew ;; (TSpawn (TApp ServerListen (ValueVar 0))) ;;*)
  (*  TNew ;; (TSend (ValueVar 2) Ping (ValueVar 0)) ;;*)
  (*  TGuard (ValueVar 1) « Pong » [*)
  (*    GReceive Pong (TGuard (ValueVar 1) 𝟙 [GFree (TValue ValueUnit)])*)
  (*  ].*)

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

  Lemma asdfe : subst (ValueUnit) 0 Client_body = Client_body.
  Proof.
    unfold Client_body.
    simpl_subst_goal; simpl.
    simpl_lift_goal; simpl.
    simpl_subst_goal. reflexivity.
  Qed.

  Compute lift 3 4 (ValueVar 3).
  Compute lift 2 1 (TLet (TValue ValueUnit) (TValue (ValueVar 1))).
  Compute subst (ValueUnit) 3 Client_body.
  Compute lift 0 4 Client_body.

  Definition ServerListen_body : Term :=
    TGuard (ValueVar 0) (« Ping » ⊕ 𝟙) [
      GReceive Ping (TLet (TSend (ValueVar 0) Pong (ValueUnit)) (TGuard (ValueVar 2) 𝟙 [GFree (TValue ValueUnit)]));
      GFree (TValue ValueUnit)
    ].

  (* TODO: Check if it makes sense for 0 arguments to be represented by unit type *)
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

  (*Lemma ServerListen_WellTyped : WellTypedDefinition PingPongProgram ServerListenDefinition.*)
  (*Proof.*)
  (*  constructor.*)
  (*  unfold ServerListen_body.*)
  (*  (*eapply GUARD with (env1 := [Some (? « Ping » ⊕ 𝟙 ^^ •)]) (env2 := [None]) (f := « Ping » ⊙ 𝟙).*)*)
  (*  eapply GUARD with (env1 := [Some (? « Ping » ⊕ 𝟙 ^^ •)]) (env2 := [None]) (f := (« Ping » ⊕ 𝟙) ⊙ 𝟙).*)
  (*  - repeat constructor.*)
  (*  - rewrite <- raw_insert_zero; repeat constructor.*)
  (*    (*eapply SUB with (T1 := (? « Ping » ^^ •)) (env2 := [Some (? « Ping » ^^ •)]).*)*)
  (*    (*+ repeat constructor.*)*)
  (*    (*  intros m mIn.*)*)
  (*    (*  admit.*)*)
  (*    (*  (*apply EnvironmentSubtype_refl.*)*)*)
  (*    (*+ repeat constructor.*)*)
  (*    (*  apply MPComp_MPInclusion_One.*)*)
  (*    (*+ rewrite <- raw_insert_zero.*)*)
  (*    (*  repeat constructor.*)*)
  (*  - constructor. econstructor.*)
  (*    + simpl; reflexivity.*)
  (*    + now right.*)
  (*    + eapply LET with*)
  (*        (T1 := TTBase BTUnit)*)
  (*        (env1 := (insert 0 (! « Pong » ^^ ◦) [None; None]))*)
  (*        (env2 := (insert 1 (? 𝟙 ^^ •) [None; None])).*)
  (*      * repeat rewrite raw_insert_successor.*)
  (*        repeat rewrite raw_insert_zero.*)
  (*        simpl.*)
  (*        rewrite lookup_zero.*)
  (*        repeat constructor.*)
  (*      * simpl.*)
  (*        eapply SEND with*)
  (*          (env1 := insert 0 (! « Pong » ^^ ◦) [None ; None])*)
  (*          (env2 := [None; None ; None]).*)
  (*        -- repeat constructor.*)
  (*        -- simpl; reflexivity.*)
  (*        -- repeat rewrite raw_insert_zero; repeat constructor.*)
  (*        -- simpl.*)
  (*           constructor; repeat constructor.*)
  (*      * eapply GUARD with*)
  (*          (f := 𝟙)*)
  (*          (env1 := insert 2 (? 𝟙 ^^ •) [None; None; None])*)
  (*          (env2 := insert 0 (TUBase BTUnit) [None; None; None]).*)
  (*        -- repeat rewrite raw_insert_successor.*)
  (*           repeat rewrite raw_insert_zero.*)
  (*           simpl.*)
  (*           repeat rewrite lookup_zero.*)
  (*           repeat constructor.*)
  (*        -- constructor; repeat constructor.*)
  (*        -- do 2 constructor.*)
  (*           eapply SUB with (env2 := repeat None 4).*)
  (*           ++ simpl; rewrite raw_insert_zero; repeat constructor.*)
  (*           ++ apply Subtype_refl.*)
  (*           ++ simpl; repeat constructor.*)
  (*        -- reflexivity.*)
  (*        -- repeat constructor.*)
  (*  - apply MPComp_MPInclusion_One.*)
  (*  - repeat constructor; econstructor.*)
  (*    + repeat constructor.*)
  (*    + rewrite MPComp_zero_right.*)
  (*      rewrite MPChoice_unit.*)
  (*      now rewrite MPComp_unit.*)
  (*Qed.*)

  (*Lemma Client_body_WellTyped : WellTypedTerm PingPongProgram [] Client_body (TUBase BTUnit).*)
  (*Proof.*)
  (*  unfold Client_body.*)
  (*  eapply LET with*)
  (*    (T1 := TTMailbox (? 𝟙))*)
  (*    (env1 := [])*)
  (*    (env2 := []).*)
  (*  - repeat constructor.*)
  (*  - repeat constructor; reflexivity.*)
  (*  - simpl.*)
  (*    eapply LET with*)
  (*      (T1 := TTBase BTUnit)*)
  (*      (env1 := [Some (? (« Ping » ⊕ 𝟙) ⊙ 𝟙 ^^ ◦)])*)
  (*      (env2 := [Some (! (« Ping » ⊕ 𝟙) ^^ •)]).*)
  (*    + repeat rewrite raw_insert_zero; repeat constructor.*)
  (*    + apply SPAWN with (env := [Some (? (« Ping » ⊕ 𝟙) ⊙ 𝟙 ^^ •)]).*)
  (*      * eapply APP; simpl; try reflexivity.*)
  (*        eapply SUB with (T1 := ? (« Ping » ⊕ 𝟙) ⊙ 𝟙 ^^ •).*)
  (*        apply EnvironmentSubtype_refl.*)
  (*        constructor. intros m mIn. now rewrite MPComp_unit in mIn.*)
  (*        constructor.*)
  (*        rewrite <- raw_insert_zero; repeat constructor.*)
  (*      * reflexivity.*)
  (*    + simpl.*)
  (*      eapply LET with*)
  (*        (T1 := TTMailbox (? 𝟙))*)
  (*        (env1 := [None; None])*)
  (*        (env2 := insert 0 (TUBase BTUnit) [Some (! « Ping » ⊕ 𝟙 ^^ •)]).*)
  (*      * repeat rewrite raw_insert_zero; repeat constructor.*)
  (*      * apply NEW; repeat constructor.*)
  (*      * simpl.*)
  (*        eapply LET with*)
  (*          (T1 := TTBase BTUnit)*)
  (*          (env1 := [Some (! « Pong » ^^ ◦); Some (TUBase BTUnit); Some (! « Ping » ⊕ 𝟙 ^^ •)])*)
  (*          (env2 := [Some (? « Pong » ⊙ 𝟙 ^^ •); None; None]).*)
  (*        -- repeat rewrite raw_insert_zero; repeat constructor.*)
  (*        -- eapply SEND with*)
  (*            (env1 := [None; None; Some (! « Ping » ⊕ 𝟙 ^^ •)])*)
  (*            (env2 := [Some (! « Pong » ^^ ◦); Some (TUBase BTUnit); None]).*)
  (*          ++ eapply SUB with (env2 := [None; None; Some (! « Ping » ^^ ◦)]).*)
  (*             ** now repeat constructor.*)
  (*             ** apply Subtype_refl.*)
  (*             ** replace [None; None; Some (! « Ping » ^^ ◦)] with (insert 2 (! « Ping » ^^ ◦) [None; None])*)
  (*                by (repeat rewrite raw_insert_successor; simpl; rewrite lookup_zero; now rewrite raw_insert_zero).*)
  (*                repeat constructor.*)
  (*          ++ simpl; reflexivity.*)
  (*          ++ repeat constructor.*)
  (*          ++ simpl.*)
  (*             eapply SUB with (env2 := [Some (! « Pong » ^^ ◦); None; None]).*)
  (*             ** do 2 constructor; try reflexivity; now repeat constructor.*)
  (*             ** apply Subtype_refl.*)
  (*             ** rewrite <- raw_insert_zero; repeat constructor.*)
  (*        -- eapply SUB with (env2 := [None; Some (? « Pong » ⊙ 𝟙 ^^ •); None; None]).*)
  (*           ++ rewrite raw_insert_zero; repeat constructor; reflexivity.*)
  (*           ++ apply Subtype_refl.*)
  (*           ++ eapply GUARD with*)
  (*                (env1 := insert 1 (? « Pong » ⊙ 𝟙 ^^ •) [None; None; None])*)
  (*                (env2 := [None; None; None; None]).*)
  (*             ** rewrite raw_insert_successor; rewrite raw_insert_zero; rewrite lookup_zero; simpl.*)
  (*                repeat constructor.*)
  (*             ** repeat constructor.*)
  (*             ** constructor.*)
  (*                eapply RECEIVE.*)
  (*                --- simpl; reflexivity.*)
  (*                --- now left.*)
  (*                --- eapply GUARD with*)
  (*                      (env1 := insert 1 (? 𝟙 ^^ •) [Some (TUBase BTUnit); None; None; None; None])*)
  (*                      (env2 := [None; None; None; None; None; None]).*)
  (*                    +++ rewrite raw_insert_successor.*)
  (*                        repeat rewrite raw_insert_zero.*)
  (*                        rewrite lookup_zero; simpl.*)
  (*                        repeat constructor.*)
  (*                    +++ eapply SUB with (env2 := insert 1 (? 𝟙 ^^ •) [None; None; None; None; None]).*)
  (*                        repeat rewrite raw_insert_successor;*)
  (*                        repeat rewrite raw_insert_zero.*)
  (*                        repeat rewrite lookup_zero; simpl; repeat constructor; reflexivity.*)
  (*                        apply Subtype_refl.*)
  (*                        repeat constructor.*)
  (*                    +++ repeat constructor.*)
  (*                    +++ reflexivity.*)
  (*                    +++ repeat constructor.*)
  (*             ** apply MPComp_MPInclusion_One.*)
  (*             ** constructor; econstructor.*)
  (*                repeat constructor.*)
  (*                rewrite MPComp_unit.*)
  (*                rewrite MPComp_zero_right.*)
  (*                now rewrite MPChoice_unit.*)
  (*Qed.*)

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

  Theorem PingPongProgram_WellTyped : WellTypedProgram PingPongProgram.
  Proof.
    constructor.
    - intros [|].
      + apply Client_Welltyped.
      + apply ServerListen_WellTyped.
    - simpl.

End ping_pong_example.

(*
  def client() : 1 {
    let server = new in
    spawn server_init();
    let self = new in
    server!Connect[self];
    guard self : _ {
      receive Ack[r] from self |-> client_beat(self, r)
    }
  }

  def client_beat(self, server) {
    server!Beat[self];
    guard self : _ {
      receive Beat[r] from self |-> client_beat(self, r)
      receive Close[r] from self |-> 
    }
  }
*)
(**)
(*Section heartbeat.*)
(**)
(*  Inductive Heartbeat : Type :=*)
(*    | StartHearbeat : Heartbeat*)
(*    | Beat : Heartbeat*)
(*    | Close : Heartbeat*)
(*    | Ack : Heartbeat.*)
(**)
(*  Instance HeartbeatMessage : IMessage Heartbeat.*)
(*  Proof.*)
(*    constructor.*)
(*    - destruct m, n; try (now left); try (now right).*)
(*    - apply (fun _ => 1).*)
(*  Defined.*)
(**)
(*  Definition StartHeartbeatType := ? (⋆ « Beat » ⊕ « Close »).*)
(*  Definition BeatType := TTBase (BTUnit).*)
(*  Definition CloseType := ? « Ack ».*)
(*  Definition AckType := TTBase (BTUnit).*)
(**)
(*  Definition HeartbeatMessage_Types (m : Heartbeat) :=*)
(*    match m with*)
(*    | StartHearbeat => TTMailbox (? (⋆ « Beat » ⊕ « Close »))*)
(*    | Close => TTMailbox (? « Ack »)*)
(*    | _ => TTBase BTUnit*)
(*    end.*)
(**)
(*End heartbeat.*)
(**)
(**)
(*Section ping_pong_example.*)
(**)
(*  Inductive PingPong : Type :=*)
(*    | Ping  : PingPong*)
(*    | Pong  : PingPong*)
(*    | Abort : PingPong*)
(*    | Ack   : PingPong.*)
(**)
(*  Instance PingPongMessage : IMessage PingPong.*)
(*  Proof.*)
(*    constructor.*)
(*    - destruct m, n; try (now left); try (now right).*)
(*    - apply (fun _ => 1).*)
(*  Defined.*)
(**)
(*  Definition PingType := ! « Pong ».*)
(*  Definition PongType := TTBase (BTUnit).*)
(*  Definition AbortType := ? «  ».*)
(**)
(*End ping_pong_example.*)
(**)
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

(** Definition of the function emptyFuture from the paper
    emptyFuture : EmptyFutureType -> 1
*)
Definition EmptyFutureBody : Term :=
  TGuard (ValueVar 0) (« Put » ⊙ (⋆ « Get »)) [
    GReceive Put (TValue (ValueVar 0)) (TApp FullFutureDef [ValueVar 1; ValueVar 0])
  ].

Definition EmptyFuture : FunctionDefinition :=
  FunDef EmptyFutureDef [ EmptyFutureType ^^ • ] (TUBase BTUnit) EmptyFutureBody.

(** Definition of the function fullFuture from the paper
    fullFuture : FullFutureType -> 1
*)
Definition FullFutureBody : Term :=
  TGuard (ValueVar (Var 1)) (⋆ « Get ») [
    GFree (TValue ValueUnit) ;
    GReceive Get (Var 1)
      (TLet
        (TSend (ValueVar (Var 0)) Reply [(ValueVar (Var 2))])
        (TApp FullFutureDef [ValueVar (Var 2) ; ValueVar (Var 3)])
      )
  ].

Definition FullFuture : FunctionDefinition :=
  FunDef FullFutureDef [ FullFutureType ^^ • ; (TUBase BTBool) ] (TUBase BTUnit) FullFutureBody.

(** Definition of the function client from the paper
    client : 1
*)
Definition ClientBody : Term :=
  TLet
    (TNew)
    (TLet
      (TSpawn (TApp EmptyFutureDef [ValueVar (Var 0)]))
      (TLet
        (TNew)
        (TLet
          (TSend (ValueVar (Var 2)) Put [ValueBool true])
          (TLet
            (TSend (ValueVar (Var 3)) Get [ValueVar (Var 1)])
            (TGuard (ValueVar (Var 2)) (« Reply ») [
              GReceive Reply (Var 2) (
                (TLet
                  (TGuard (ValueVar (Var 1)) 𝟙 [(GFree (TValue ValueUnit))])
                  (TValue ValueUnit)
                )
              )]
            )
          )
        )
      )
    ).

Definition Client : FunctionDefinition :=
  FunDef ClientDef [] (TUBase BTUnit) ClientBody.

(** Defining the function returning function definitons *)
Definition FutureDefinitions (d : FutureDefinition) : FunctionDefinition :=
  match d with
  | EmptyFutureDef => FunDef EmptyFutureDef [EmptyFutureType ^^ •] (TUBase BTUnit) EmptyFutureBody
  | FullFutureDef => FunDef FullFutureDef [FullFutureType ^^ •; (TUBase BTBool)] (TUBase BTUnit) FullFutureBody
  | ClientDef => FunDef ClientDef [] (TUBase BTUnit) ClientBody
  end.

Definition FutureProgram :=
  {|
    signature := FutureMessageTypes
  ; definitions := FutureDefinitions
  ; initialTerm := ClientBody
  |}.

(*Compute FV EmptyFutureBody.*)
(*Compute FV FullFutureBody.*)
(*Compute FV ClientBody.*)

(** Function emptyFuture is well-typed
    |- emptyFuture
*)
Lemma EmptyFutureWellTyped :
  WellTypedDefinition FutureProgram EmptyFuture.
Proof.
  unfold EmptyFuture. unfold EmptyFutureBody.
  eapply FUNDEF; simpl.
  eapply GUARD with (env2 := (None :: nil)) (env1 := (Some (EmptyFutureType ^^ •)) :: nil) (f := (« Put » ⊙ ⋆ « Get »)).
  - simpl. repeat constructor.
  - constructor; simpl. constructor. f_equal.
  - constructor. apply RECEIVE with (tList := FutureMessageTypes Put).
    + easy.
    + right. constructor.
    + simpl.
      eapply APP with
        (envList := ((None :: Some (FullFutureType ^^ •) :: None :: nil) :: (Some (TUBase BTBool) :: None :: None :: nil) :: nil)).
      * easy.
      * repeat constructor.
      * simpl. constructor.
        -- constructor. simpl. repeat constructor. now simpl.
        -- constructor.
           ++ constructor. simpl. repeat constructor. now simpl.
           ++ constructor.
  - apply MPInclusion_refl.
  - constructor.
    eapply PNFLitComp.
    + apply MPResComp.
      * constructor.
      * constructor. constructor. easy.
    + rewrite MPComp_zero_left.
      rewrite MPComp_zero_right.
      rewrite MPComp_comm.
      rewrite MPComp_unit.
      now rewrite MPChoice_unit.
Qed.

(** Function emptyFuture is well-typed
    |- emptyFuture
*)
Lemma FullFutureWellTyped :
  WellTypedDefinition FutureProgram FullFuture.
Proof.
  constructor.
  simpl.
  eapply GUARD with
    (env1 := None :: Some (FullFutureType ^^ •) :: nil)
       (env2 := Some (TUBase BTBool) :: None :: nil)
    (f := 𝟙 ⊕ (« Get » ⊙ (⋆ « Get »))).
  - repeat constructor.
  - eapply SUB with (env2 := None :: Some (FullFutureType ^^ •) :: nil).
    + do 3 constructor.
      apply MPInclusion_refl.
      repeat constructor.
    + constructor.
      * apply MPStar_MPInclusion_rec.
      * constructor.
    + repeat constructor.
  - constructor.
    + constructor.
      eapply SUB with (env2 := None :: None :: nil) (T1 := TUBase BTUnit).
      * repeat constructor.
      * constructor.
      * apply UNIT. repeat constructor.
    + constructor.
      apply RECEIVE with (tList := FutureMessageTypes Get).
      * easy.
      * now right.
      * simpl. eapply LET with
        (env1 := Some (! « Reply » ^^ ◦) :: None :: Some (TUBase BTBool) :: None :: nil)
        (env2 := (None :: Some (? ⋆ « Get » ^^ •) :: Some (TUBase BTBool) :: None :: nil))
        (T1 := TTBase BTUnit).
        -- simpl. repeat constructor.
        -- simpl. eapply SEND with
           (env' := Some (! « Reply » ^^ ◦) :: None :: None :: None :: nil).
           ++ repeat constructor.
           ++ now simpl.
           ++ repeat constructor.
           ++ simpl. repeat constructor.
        -- simpl. apply SUB with
           (env2 := None :: None :: Some (? ⋆ « Get » ^^ •) :: Some (TUBase BTBool) :: None :: nil)
           (T1 := TUBase BTUnit).
           ** do 4 constructor.
              apply MPInclusion_refl.
              all: repeat constructor.
           ** constructor.
           ** eapply APP with
              (envList := (None :: None :: Some (? ⋆ « Get » ^^ •) :: None :: None :: nil)
               :: (None :: None :: None :: Some (TUBase BTBool) :: None :: nil) :: nil).
              --- easy.
              --- repeat constructor.
              --- repeat constructor.
  - apply MPStar_MPInclusion_rec.
  - constructor. constructor.
    + constructor.
    + eapply PNFLitComp.
      * repeat constructor.
      * rewrite MPComp_comm.
        rewrite MPComp_unit.
        rewrite MPChoice_comm.
        rewrite MPChoice_unit.
        apply MPStar_rec.
Qed.

Lemma ClientBodyWellTyped : WellTypedTerm FutureProgram [] ClientBody (TUBase BTUnit).
Proof.
  eapply LET with (T1 := TTMailbox (? 𝟙)); simpl.
  - constructor.
  - apply NEW; constructor.
  - eapply LET with (T1 := TTBase BTUnit); simpl.
    + apply EnvCombBoth with
        (T1 := ? ((« Put » ⊙  « Get ») ⊙  𝟙) ^^ ◦)
        (T2 := ! (« Put » ⊙  « Get ») ^^ •).
      * constructor.
      * constructor. constructor.
        apply TCombOutIn.
    + apply SUB with
        (T1 := TUBase BTUnit)
        (env2 := Some (? (« Put » ⊙  ⋆ « Get ») ^^ ◦) :: nil).
      * repeat constructor.
        (* TODO: Move into own lemma *)
        intros m mIn.
        rewrite MPComp_unit in mIn.
        inversion mIn; subst.
        eapply MPValueComp.
        apply H1.
        constructor. exists 1. simpl. rewrite MPComp_unit. apply H3.
        easy.
      * constructor.
      * assert (H : (Some (? « Put » ⊙ ⋆ « Get » ^^ ◦) :: nil) = ⌈ (Some (? « Put » ⊙ ⋆ « Get » ^^ •) :: nil) ⌉ₑ).
        { reflexivity. }
        rewrite H.
        apply SPAWN.
        eapply APP.
        -- easy.
        -- constructor.
        -- repeat constructor.
    + eapply LET with (T1 := TTMailbox (? 𝟙)) (env1 := None :: None :: nil). (*T1 := ? 𝟙 ^^ •).*)
      * repeat constructor.
      * simpl. 
        eapply SUB with (env2 := None :: None :: nil);
        repeat constructor.
        apply MPInclusion_refl.
      * eapply LET with
          (T1 := TTBase BTUnit)
          (env1 := None :: None :: Some (! « Put » ^^ ◦) :: nil).
        -- repeat constructor.
        -- eapply SEND with
             (env' := None :: None :: Some (! « Put » ^^ ◦) :: nil)
             (envList := (None :: None :: None :: nil) :: nil).
           ++ repeat constructor.
           ++ easy.
           ++ repeat constructor.
           ++ repeat constructor.
        -- eapply LET with
            (T1 := TTBase BTUnit)
            (env1 := None :: Some (! « Reply » ^^ ◦) :: None :: Some (! « Get » ^^ •) :: nil).
           ++ repeat constructor.
           ++ eapply SEND with
               (env' := None :: None :: None :: Some (! « Get » ^^ •) :: nil).
              ** eapply SUB with
                  (env2 := None :: None :: None :: Some (! « Get » ^^ ◦) :: nil).
                 --- repeat constructor. apply MPInclusion_refl.
                 --- constructor. apply MPInclusion_refl. constructor.
                 --- repeat constructor.
              ** easy.
              ** repeat constructor.
              ** repeat constructor.
           ++ eapply SUB with
                  (env2 := None :: None :: Some (? « Reply » ⊙ 𝟙 ^^ •) :: None :: None :: nil).
              ** repeat constructor. apply MPInclusion_refl.
              ** constructor.
              ** eapply GUARD with
                   (f := « Reply » ⊙ 𝟙) (env2 := None :: None :: None :: None :: None :: nil).
                 --- repeat constructor.
                 --- repeat constructor.
                 --- constructor. eapply RECEIVE.
                     +++ easy.
                     +++ right. constructor.
                     +++ simpl.
                         eapply LET with
                           (T1 := TTBase BTUnit)
                           (env1 := None :: Some (? 𝟙 ^^ •) :: None :: None :: None :: None :: None:: nil).
                           *** repeat constructor.
                           *** eapply GUARD.
                               ----  constructor. apply EnvDisCombLeft. repeat constructor.
                               ---- repeat constructor.
                               ---- repeat constructor.
                               ---- apply MPInclusion_refl.
                               ---- repeat constructor.
                           *** eapply SUB with
                                 (env2 := None :: None :: None :: None :: None :: None :: None :: None :: nil).
                               ---- repeat constructor.
                               ---- repeat constructor.
                               ---- repeat constructor.
                 --- intros m mIn. now rewrite MPComp_unit.
                 --- repeat constructor.
                     eapply PNFLitComp.
                     repeat constructor.
                     rewrite MPComp_unit.
                     rewrite MPComp_zero_right.
                     now rewrite MPChoice_unit.
Qed.

Lemma ClientWellTyped :
  WellTypedDefinition FutureProgram Client.
Proof.
  constructor.
  apply ClientBodyWellTyped.
Qed.

Lemma FutureProgramWellTyped : WellTypedProgram FutureProgram.
Proof.
  apply PROG.
  - destruct def; simpl.
    + apply EmptyFutureWellTyped.
    + apply FullFutureWellTyped.
    + apply ClientWellTyped.
  - simpl. apply ClientBodyWellTyped.
Qed.

End future_example.
