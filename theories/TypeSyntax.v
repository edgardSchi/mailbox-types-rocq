(** * Type syntax of mailbox types *)

(** Mailbox type definition *)
Inductive MType : Type :=
    MTOutput : MType
  | MTInput  : MType.

(** Mailbox pattern definition *)
Inductive MPattern : Type :=
    MPZero : MPattern
  | MPOne : MPattern
  | MPMessage : MPattern
  | MPChoice : MPattern -> MPattern -> MPattern
  | MPComp : MPattern -> MPattern -> MPattern
  | MPStar : MPattern -> MPattern.
