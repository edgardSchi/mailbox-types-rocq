Inductive WellTypedTerm (prog : Prog) : Env -> Term -> TUsage -> Prop :=
  (* Var *)
| VAR   : forall v env T,
      SingletonEnv env ->
      lookup v env = Some T ->
      WellTypedTerm prog env (TValue (ValueVar (Var v))) T
  (* Consts *)
  | TRUE  : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env (TValue (ValueBool true)) (TUBase BTBool)
  | FALSE : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env (TValue (ValueBool false)) (TUBase BTBool)
  | UNIT  : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env (TValue ValueUnit) (TUBase BTUnit)
  (* App *)
  | APP : forall env v definition bodyType argumentType term,
      definitions prog definition = (FunDef definition argumentType bodyType term) ->
      WellTypedTerm prog env (TValue v) argumentType ->
      WellTypedTerm prog env (TApp definition v) bodyType
  (* Let *)
  | LET   : forall env env1 env2 T1 T2 t1 t2, 
      env1 ▷ₑ env2 ~= env ->
      WellTypedTerm prog env1 t1 ⌊ T1 ⌋ ->
      WellTypedTerm prog (Some ⌊ T1 ⌋ :: env2) t2 T2 ->
      WellTypedTerm prog env (TLet t1 t2) T2
  (* Spawn *)
  | SPAWN : forall env t,
      WellTypedTerm prog env t (TUBase BTUnit) ->
      WellTypedTerm prog ⌈ env ⌉ₑ (TSpawn t) (TUBase BTUnit)
  (* New *)
  | NEW : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env TNew (? 𝟙 ^^ •)
  (* Send *)
  | SEND : forall env env1 env2 T m v1 v2,
      WellTypedTerm prog env1 (TValue v1) (! « m » ^^ ◦) ->
      signature prog m = T ->
      env1 +ₑ env2 ~= env ->
      WellTypedTerm prog env2 (TValue v2) ⌈ T ⌉ ->
      WellTypedTerm prog env (TSend v1 m v2) (TUBase BTUnit)
  (* Guard *)
  | GUARD : forall env env1 env2 guards v T e f,
      env1 +ₑ env2 ~= env ->
      WellTypedTerm prog env1 (TValue v) (? f ^^ •) ->
      WellTypedGuards prog env2 guards T f ->
      e ⊑ f ->
      f ⊧ f ->
      WellTypedTerm prog env (TGuard v e guards) T
  (* Sub *)
  | SUB : forall t env1 env2 T1 T2,
      env1 ≤ₑ env2 ->
      T1 ≤ T2 ->
      WellTypedTerm prog env2 t T1 ->
      WellTypedTerm prog env1 t T2
with WellTypedGuards (prog : Prog) : Env -> list Guard -> TUsage -> MPattern -> Prop :=
  | SINGLE : forall T e env g,
      WellTypedGuard prog env g T e ->
      WellTypedGuards prog env (g :: nil) T e
  | SEQ : forall T e es env guards g,
      WellTypedGuard prog env g T e ->
      WellTypedGuards prog env guards T es ->
      WellTypedGuards prog env (g :: guards) T (e ⊕ es)
with WellTypedGuard (prog : Prog) : Env -> Guard -> TUsage -> MPattern -> Prop :=
  (* Fail *)
  | FAIL : forall t env, WellTypedGuard prog env GFail t 𝟘
  (* Free *)
  | FREE : forall t env T,
      WellTypedTerm prog env t T ->
      WellTypedGuard prog env (GFree t) T 𝟙
  (* Receive *)
  | RECEIVE : forall t m env BT T e,
      signature prog m = BT ->
      BaseType BT \/ BaseEnv env ->
      WellTypedTerm prog (Some ⌈ BT ⌉ :: Some (? e ^^ •) :: env) t T ->
      WellTypedGuard prog env (GReceive m t) T (« m » ⊙ e).

Inductive WellTypedDefinition (prog : Prog) : FunctionDefinition -> Prop :=
  | FUNDEF : forall defName argumentType body bodyType,
      WellTypedTerm prog [Some argumentType] body bodyType ->
      WellTypedDefinition prog (FunDef defName argumentType bodyType body).

Inductive WellTypedProgram (prog : Prog) : Prop :=
  PROG :
    (forall def, WellTypedDefinition prog (definitions prog def)) ->
    WellTypedTerm prog nil (initialTerm prog) (TUBase BTUnit) -> WellTypedProgram prog.
