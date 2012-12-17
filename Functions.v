Require Import Ensembles.
Require Import Notations.
(*Require Import Common.*)

Set Implicit Arguments.

Section preimage.
  Variable A B : Type.
  Variable f : A -> B.

  Definition preimage (X : Ensemble B) : Ensemble A
    := (fun a => (f a) ∈ X).

  Definition image (X : Ensemble A) : Ensemble B
    := (fun b => exists a, b = f a).
End preimage.

Notation "f ⁻¹" := (preimage f).
