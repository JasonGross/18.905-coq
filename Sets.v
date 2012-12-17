Require Import Ensembles.
Require Import Notations.

Set Implicit Arguments.

Section sets.
  Variable X : Type.

  Variable C : Ensemble (Ensemble X).

  Definition union : Ensemble X :=
    (fun x => exists S, S ∈ C /\ x ∈ S).

  Definition intersection : Ensemble X :=
    (fun x => forall S, S ∈ C -> x ∈ S).
End sets.
