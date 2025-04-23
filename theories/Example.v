(** * Future example *)

From MailboxTypes Require Import TypingRules.
From MailboxTypes Require Import Util.

Require Import Lists.List.
Import ListNotations.

Section future_example.

Inductive Future : Type :=
  | Put   : Future
  | Get   : Future
  | Reply : Future.

Instance FutureMessage : IMessage Future.
Proof.
  constructor;
  destruct m; destruct n;
  try (now left);
  try (now right).
Defined.

Inductive FutureDefinition : Type :=
  | EmptyFutureDef : FutureDefinition
  | FullFutureDef  : FutureDefinition
  | ClientDef      : FutureDefinition.

Instance FutureDefinitionName : IDefinitionName FutureDefinition.
Proof.
  constructor; destruct m; destruct n;
  try (now left);
  try (now right).
Defined.

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
  TGuard (ValueVar (Var 0)) (« Put » ⊙ (⋆ « Get »)) [
    GReceive Put (Var 1) (TApp FullFutureDef [ValueVar (Var 1) ; ValueVar (Var 0)])
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
Definition FutureDefinitions (d : FutureDefinition) : (list TUsage) * TUsage * Term :=
  match d with
  | EmptyFutureDef => (((EmptyFutureType ^^ •) :: nil), (TUBase BTUnit), EmptyFutureBody)
  | FullFutureDef => (((FullFutureType ^^ •) :: (TUBase BTBool) :: nil), (TUBase BTUnit), FullFutureBody)
  | ClientDef => (nil, (TUBase BTUnit), ClientBody)
  end.

Definition FutureProgram :=
  {|
    signature := FutureMessageTypes
  ; definitions := FutureDefinitions
  ; initialTerm := ClientBody
  |}.

(** Function emptyFuture is well-typed
    |- emptyFuture
*)
Lemma EmptyFutureWellTyped :
  WellTypedDefinition FutureProgram EmptyFuture.
Proof.
  unfold EmptyFuture. unfold EmptyFutureBody.
  eapply FUNDEF; simpl.
  eapply GUARD with (env2 := (None :: nil)) (env1 := (Some (EmptyFutureType ^^ •)) :: nil) (f := (« Put » ⊙ (⋆ « Get »))).
  - simpl. repeat constructor.
  - constructor; simpl. constructor. f_equal.
  - constructor. apply RECEIVE with (tList := FutureMessageTypes Put).
    + easy.
    + right. constructor.
    + simpl.
      eapply APP
      with (argumentTypes := fst (fst (FutureDefinitions FullFutureDef)))
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

Lemma ClientWellTyped :
  WellTypedDefinition FutureProgram Client.
Proof.
  constructor.
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

End future_example.
