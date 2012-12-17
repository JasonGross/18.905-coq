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

Notation "⋃_( α ) X" := (@union _ (fun S => exists α, S = X)).
Notation "⋂_( α ) X" := (@intersection _ (fun S => exists α, S = X)).
Notation "A ∪ B" := (@union _ (fun S => S = A \/ S = B)).
Notation "A ∩ B" := (@union _ (fun S => S = A \/ S = B)).
