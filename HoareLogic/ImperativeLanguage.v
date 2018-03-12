Class ProgrammingLanguage cmd : Type := {
  normal_form: cmd -> Prop;
}.

Class ControlStack stack : Type := {
  empty_stack: stack;
}.

Class Continuation cont {cmd stack} {P: ProgrammingLanguage cmd} {CS: ControlStack stack}: Type := {
  Ceval: cmd -> stack -> cont;
  Creturn: cmd -> stack -> cont;
}.

Class LinearControlStack stack {CS: ControlStack stack}: Type := {
  frame: Type;
  cons: frame -> stack -> stack;
}.

Class ImperativeProgrammingLanguage cmd {P: ProgrammingLanguage cmd}: Type := {
  bool_expr: Type;
  Ssequence: cmd -> cmd -> cmd;
  Sifthenelse: bool_expr -> cmd -> cmd -> cmd;
  Swhile: bool_expr -> cmd -> cmd;
  Sskip: cmd
}.

Class ImperativeProgrammingLanguageContinuation {cmd stack} cont {P: ProgrammingLanguage cmd} {CS: ControlStack stack} {Cont: Continuation cont} {iP: ImperativeProgrammingLanguage cmd} {lCS: LinearControlStack stack}: Type := {
  Fsequence: cmd -> frame;
  Fwhile: bool_expr -> cmd -> frame;
}.

Class ImperativeProgrammingLanguage_SbreakScontinue cmd {P: ProgrammingLanguage cmd}: Type := {
  Sbreak: cmd;
  Scontinue: cmd;
}.

(* comment for future reconstruction
Class ConcurrentProgrammingLanguage_Sparallel (P: ProgrammingLanguage): Type := {
  Sparallel: cmd -> cmd -> cmd
}.

Class Resource: Type := {
  resource: Type;
  resources := resource -> Prop
}.

Class ConcurrentProgrammingLanguage_Sresource (P: ProgrammingLanguage) (Res: Resource): Type := {
  Sresource: resource -> cmd -> cmd
}.

Class ConcurrentProgrammingLanguage_AcqRel_resource (P: ProgrammingLanguage) (Res: Resource): Type := {
  Sacquire_res: resource -> cmd;
  Srelease_res: resource -> cmd
}.

Class ConcurrentProgrammingLanguage_lock (P: ProgrammingLanguage): Type := {
  lock_expr: Type
}.

Class ConcurrentProgrammingLanguage_AcqRel_lock (P: ProgrammingLanguage) {CPl: ConcurrentProgrammingLanguage_lock P}: Type := {
  Sacquire_lock: lock_expr -> cmd;
  Srelease_lock: lock_expr -> cmd
}.

Class NormalImperativeProgrammingLanguage (P: ProgrammingLanguage) {iP: ImperativeProgrammingLanguage P}: Type := {
  Ssequence_inv: forall c1 c2 c1' c2', Ssequence c1 c2 = Ssequence c1' c2' -> c1 = c1' /\ c2 = c2';
  Ssequence_Sskip: forall c1 c2, Ssequence c1 c2 <> Sskip;
  Sifthenelse_inv: forall b c1 c2 b' c1' c2', Sifthenelse b c1 c2 = Sifthenelse b' c1' c2' -> b = b' /\ c1 = c1' /\ c2 = c2';
  Sifthenelse_Sskip: forall b c1 c2, Sifthenelse b c1 c2 <> Sskip;
  Swhile_inv: forall b c b' c', Swhile b c = Swhile b' c' -> b = b' /\ c = c';
  Swhile_Sskip: forall b c, Swhile b c <> Sskip;
  Ssequence_Swhile: forall c1 c2 b c, Ssequence c1 c2 <> Swhile b c
}.

*)