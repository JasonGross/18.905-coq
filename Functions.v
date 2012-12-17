Require Import Ensembles.
Require Import Notations.
(*Require Import Common.*)

Set Implicit Arguments.

Section preimage.
  Variable A B : Type.
  Variable f : A -> B.

  Definition preimage (X : Ensemble B) : Ensemble A
    := (fun a => (f a) ∈ X).
End preimage.

Notation "f ⁻¹" := (preimage f).
