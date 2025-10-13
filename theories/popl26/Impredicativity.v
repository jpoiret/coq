Set Universe Polymorphism.

Inductive Box@{s;l} (A: 𝒰@{s;l}): Prop := box : A -> Box A.
Arguments box {A}.

Inductive Unbox@{s;l} (A: Prop): 𝒰@{s;l} := unbox : A -> Unbox A.
Arguments unbox {A}.

Definition resize@{s;l_1 l_2} (A: 𝒰@{s;l_1}): 𝒰@{s;l_2} := Unbox@{s;l_2} (Box@{s;l_1} A).

Definition r@{s;l_1 l_2} {A: 𝒰@{s;l_1}} (x: A) : resize@{s;l_1 l_2} A := unbox (box x).

(* In this version, we decided to explicitly disable eliminations from Prop to any sort `s`, since
  it is not clear whether to preserve this inheritance of impredicativity from Prop.
*)
Fail Definition i@{s;l_1 l_2 | Prop ~> s} {A: 𝒰@{s;l_1}} (x: resize@{s;l_1 l_2} A): A :=
  match x with unbox (box x) => x end.

Fail Definition impredPi@{s_1 s_2;l_1 l_2 | Prop ~> s_2}
  (A: 𝒰@{s_1;l_1}) (B: A -> 𝒰@{s_2;l_2}) : 𝒰@{s_2;l_2} := resize (forall (x: A), B x).
