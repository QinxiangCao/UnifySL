Class ImperativeProgrammingLanguage: Type := {
  cmd: Type
}.

Class NormalImperativeProgrammingLanguage (Imp: ImperativeProgrammingLanguage): Type := {
  Ssequence: cmd -> cmd -> cmd
}.

Class SmallStepSemantics (Imp: ImperativeProgrammingLanguage): Type := {
  state: Type;
  step: cmd * state -> cmd * state -> Prop
}.
