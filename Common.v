Require Import JMeq ProofIrrelevance.

Set Implicit Arguments.

Local Infix "==" := JMeq (at level 70).

(* The standard library does not provide projections of [sigT2] or [sig2].
   I define coercions to [sigT] and [sig], so that [projT1], [projT2],
   [proj1_sig], and [proj2_sig] do the right thing, and I define [projT3],
   [proj3_sig]. *)
Section sig.
  Definition sigT_of_sigT2 A P Q (x : @sigT2 A P Q) := let (a, h, _) := x in existT _ a h.
  Global Coercion sigT_of_sigT2 : sigT2 >-> sigT.
  Definition projT3 A P Q (x : @sigT2 A P Q) :=
    let (x0, _, h) as x0 return (Q (projT1 x0)) := x in h.

  Definition sig_of_sig2 A P Q (x : @sig2 A P Q) := let (a, h, _) := x in exist _ a h.
  Global Coercion sig_of_sig2 : sig2 >-> sig.
  Definition proj3_sig A P Q (x : @sig2 A P Q) :=
    let (x0, _, h) as x0 return (Q (proj1_sig x0)) := x in h.
End sig.

(* fail if [tac] succeeds, do nothing otherwise *)
Tactic Notation "not_tac" tactic(tac) := (tac; fail 1) || idtac.

(* fail if [tac] fails, but don't actually execute [tac] *)
Tactic Notation "test_tac" tactic(tac) := not_tac (not_tac tac).

(* fail if [x] is a function application, a dependent product ([fun _ => _]),
   or a sigma type ([forall _, _]) *)
Ltac atomic x :=
  match x with
    | ?f _ => fail 1 x "is not atomic"
    | (fun _ => _) => fail 1 x "is not atomic"
    | forall _, _ => fail 1 x "is not atomic"
    | _ => idtac
  end.

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Ltac unique_pose defn :=
  let T := type of defn in
    match goal with
      | [ H : T |- _ ] => fail 1
      | _ => pose proof defn
    end.

(* [pose defn], but only if that hypothesis doesn't exist *)
Ltac unique_pose_with_body defn :=
  match goal with
    | [ H := defn |- _ ] => fail 1
    | _ => pose defn
  end.

(* check's if the given hypothesis has a body, i.e., if [clearbody]
   could ever succeed.  We can't just do [test_tac (clearbody H)],
   because maybe the correctness of the proof depends on the body
   of H *)
Tactic Notation "has_no_body" hyp(H) :=
  not_tac (let H' := fresh in pose H as H'; unfold H in H').

Tactic Notation "has_body" hyp(H) :=
  not_tac (has_no_body H).

(* find the head of the given expression *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(* call [tac H], but first [simpl]ify [H].
   This tactic leaves behind the simplified hypothesis. *)
Ltac simpl_do tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'.

(* clear the left-over hypothesis after [simpl_do]ing it *)
Ltac simpl_do_clear tac H := simpl_do ltac:(fun H => tac H; try clear H) H.

Ltac do_with_hyp tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.

(* some simple tactics to solve the goal by rewriting *)
Ltac t' := repeat progress (simpl in *; intros; try split; trivial).
Ltac t'_long := repeat progress (simpl in *; intuition).

Ltac t_con_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_con_rev_with con tac := tac;
  repeat (match goal with
            | [ H : context[con] |- _ ] => rewrite <- H
            | _ => progress autorewrite with core in *
          end; tac).

Ltac t_with tac := t_con_with @eq tac.

Ltac t_rev_with tac := t_con_rev_with @eq tac.

Ltac t_con con := t_con_with con t'; t_con_with con t'_long.
Ltac t_con_rev con := t_con_rev_with con t'; t_con_rev_with con t'_long.

Ltac t := t_with t'; t_with t'_long.
Ltac t_rev := t_rev_with t'; t_rev_with t'_long.

(* solve simple setiod goals that can be solved by [transitivity] *)
Ltac simpl_transitivity :=
  try solve [ match goal with
                | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

(* given a [matcher] that succeeds on some hypotheses and fails on
   others, destruct any matching hypotheses, and then execute [tac]
   after each [destruct].

   The [tac] part exists so that you can, e.g., [simpl in *], to
   speed things up. *)
Ltac destruct_all_matches_then matcher tac :=
  repeat match goal with
           | [ H : ?T |- _ ] => matcher T; destruct H; tac
         end.

Ltac destruct_all_matches matcher := destruct_all_matches_then matcher ltac:(simpl in *).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
    | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
    | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac destruct_head_hnf_matcher T HT :=
  match head_hnf HT with
    | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(destruct_head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(destruct_head_hnf_matcher T).

Ltac destruct_hypotheses_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | ex _ => idtac
      | and _ _ => idtac
      | prod _ _ => idtac
    end.
Ltac destruct_hypotheses := destruct_all_matches destruct_hypotheses_matcher.
Ltac destruct_hypotheses' := destruct_all_matches' destruct_hypotheses_matcher.

Ltac destruct_sig_matcher HT :=
  let HT' := eval hnf in HT in
    match HT' with
      | @sig _ _ => idtac
      | @sigT _ _ => idtac
      | @sig2 _ _ _ => idtac
      | @sigT2 _ _ _ => idtac
    end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
  destruct_hypotheses_matcher HT || destruct_sig_matcher HT
).

(* if progress can be made by [exists _], but it doesn't matter what
   fills in the [_], assume that something exists, and leave the two
   goals of finding a member of the apropriate type, and proving that
   all members of the appropriate type prove the goal *)
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @ex;
  match goal with
    | [ |- @ex ?T _ ] => destruct_exists' T
    | [ |- @sig ?T _ ] => destruct_exists' T
    | [ |- @sigT ?T _ ] => destruct_exists' T
    | [ |- @sig2 ?T _ _ ] => destruct_exists' T
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
  end.

(* if the goal can be solved by repeated specialization of some
   hypothesis with other [specialized] hypotheses, solve the goal
   by brute force *)
Ltac specialized_assumption tac := tac;
  match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption tac
    | _ => assumption
  end.

(* for each hypothesis of type [H : forall _ : ?T, _], if there is exactly
   one hypothesis of type [H' : T], do [specialize (H H')]. *)
Ltac specialize_uniquely :=
  repeat match goal with
           | [ x : ?T, y : ?T, H : _ |- _ ] => test_tac (specialize (H x)); fail 1
           | [ x : ?T, H : _ |- _ ] => specialize (H x)
         end.

(* specialize all hypotheses of type [forall _ : ?T, _] with
   appropriately typed hypotheses *)
Ltac specialize_all_ways_forall :=
  repeat match goal with
           | [ x : ?T, H : forall _ : ?T, _ |- _ ] => unique_pose (H x)
         end.

(* try to specialize all hypotheses with all other hypotheses.
   This includes [specialize (H x)] where [H x] requires a coercion
   from the type of [H] to Funclass. *)
Ltac specialize_all_ways :=
  repeat match goal with
           | [ x : ?T, H : _ |- _ ] => unique_pose (H x)
         end.

(* try to do [tac] after [repeat rewrite] on [rew_H], in both directions *)
Ltac try_rewrite rew_H tac :=
  (repeat rewrite rew_H; tac) ||
    (repeat rewrite <- rew_H; tac).

Ltac try_rewrite_by rew_H by_tac tac :=
  (repeat rewrite rew_H by by_tac; tac) ||
    (repeat rewrite <- rew_H by by_tac; tac).

Ltac try_rewrite_repeat rew_H tac :=
  (repeat (rewrite rew_H; tac)) ||
    (repeat (rewrite <- rew_H; tac)).

Ltac solve_repeat_rewrite rew_H tac :=
  solve [ repeat (rewrite rew_H; tac) ] ||
    solve [ repeat (rewrite <- rew_H; tac) ].

Lemma sig_eq A P (s s' : @sig A P) : proj1_sig s = proj1_sig s' -> s = s'.
  destruct s, s'; simpl; intro; subst; f_equal; apply proof_irrelevance.
Qed.

Lemma sig2_eq A P Q (s s' : @sig2 A P Q) : proj1_sig s = proj1_sig s' -> s = s'.
  destruct s, s'; simpl; intro; subst; f_equal; apply proof_irrelevance.
Qed.

Lemma sigT_eq A P (s s' : @sigT A P) : projT1 s = projT1 s' -> projT2 s == projT2 s' -> s = s'.
  destruct s, s'; simpl; intros; firstorder; repeat subst; reflexivity.
Qed.

Lemma sigT2_eq A P Q (s s' : @sigT2 A P Q) :
  projT1 s = projT1 s'
  -> projT2 s == projT2 s'
  -> projT3 s == projT3 s'
  -> s = s'.
  destruct s, s'; simpl; intros; firstorder; repeat subst; reflexivity.
Qed.

Lemma injective_projections_JMeq (A B A' B' : Type) (p1 : A * B) (p2 : A' * B') :
  fst p1 == fst p2 -> snd p1 == snd p2 -> p1 == p2.
Proof.
  destruct p1, p2; simpl; intros H0 H1; subst;
    rewrite H0; rewrite H1; reflexivity.
Qed.

Ltac clear_refl_eq :=
  repeat match goal with
           | [ H : ?x = ?x |- _ ] => clear H
         end.

(* reduce the proving of equality of sigma types to proving equality
   of their components *)
Ltac simpl_eq' :=
  apply sig_eq
        || apply sig2_eq
        || ((apply sigT_eq || apply sigT2_eq); intros; clear_refl_eq)
        || apply injective_projections
        || apply injective_projections_JMeq.

Ltac simpl_eq := intros; repeat (
  simpl_eq'; simpl in *
).

(* Coq's build in tactics don't work so well with things like [iff]
   so split them up into multiple hypotheses *)
Ltac split_in_context ident funl funr :=
  repeat match goal with
           | [ H : context p [ident] |- _ ] =>
             let H0 := context p[funl] in let H0' := eval simpl in H0 in assert H0' by (apply H);
               let H1 := context p[funr] in let H1' := eval simpl in H1 in assert H1' by (apply H);
                 clear H
         end.

Ltac split_iff := split_in_context iff (fun a b : Prop => a -> b) (fun a b : Prop => b -> a).

Ltac split_and' :=
  repeat match goal with
           | [ H : ?a /\ ?b |- _ ] => let H0 := fresh in let H1 := fresh in
             assert (H0 := proj1 H); assert (H1 := proj2 H); clear H
         end.
Ltac split_and := split_and'; split_in_context and (fun a b : Prop => a) (fun a b : Prop => b).

Ltac clear_hyp_of_type type :=
  repeat match goal with
           | [ H : type |- _ ] => clear H
         end.

(* If [conVar] is not mentioned in any hypothesis other than [hyp],
   nor in the goal, then clear any hypothesis of the same type as [hyp] *)
Ltac clear_hyp_unless_context hyp conVar :=
  let hypT := type of hyp in
    match goal with
      | [ H0 : hypT, H : context[conVar] |- _ ] => fail 1 (* there is a hypotheses distinct from [hyp] which mentions [conVar] *)
      | [ |- context[conVar] ] => fail 1
      | _ => clear_hyp_of_type hypT
    end.

Ltac recur_clear_context con :=
  repeat match goal with
           | [ H : appcontext[con] |- _ ] =>
             recur_clear_context H; try clear H
           | [ H := appcontext[con] |- _ ] =>
             recur_clear_context H; try clear H
         end.

(* equivalent to [idtac] if [subexpr] appears nowhere in [expr],
   equivalent to [fail] otherwise *)
Ltac FreeQ expr subexpr :=
  match expr with
    | appcontext[subexpr] => fail 1
    | _ => idtac
  end.

Ltac subst_mor x :=
  match goal with
    | [ H : ?Rel ?a x |- _ ] => FreeQ a x; rewrite <- H in *;
      try clear_hyp_unless_context H x
    | [ H : ?Rel x ?a |- _ ] => FreeQ a x; rewrite H in *;
      try clear_hyp_unless_context H x
  end.

Ltac repeat_subst_mor_of_type type :=
  repeat match goal with
           | [ m : context[type] |- _ ] => subst_mor m; try clear m
         end.

Ltac subst_body :=
  repeat match goal with
           | [ H := _ |- _ ] => subst H
         end.

(* So we know the difference betwen the [sigT]s we're using and the [sigT]s others use *)
Inductive Common_sigT (A : Type) (P : A -> Type) : Type :=
    Common_existT : forall x : A, P x -> Common_sigT P.
Definition Common_projT1 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (a, _) := x in a.
Definition Common_projT2 (A : Type) (P : A -> Type) (x : @Common_sigT A P) := let (x0, h) as x0 return (P (Common_projT1 x0)) := x in h.

Ltac uncurryT H :=
  match eval simpl in H with
    | forall (x : ?T1) (y : @?T2 x), @?f x y => uncurryT (forall xy : @Common_sigT T1 T2, f (Common_projT1 xy) (Common_projT2 xy))
    | ?H' => H'
  end.

Ltac curryT H :=
  match eval simpl in H with
    | forall xy : @Common_sigT ?T1 ?T2, @?f xy => curryT (forall (x : T1) (y : T2 x), f (@Common_existT T1 T2 x y))
    | ?H' => H'
  end.

Ltac uncurry H := let HT := type of H in
  match eval simpl in HT with
    | forall (x : ?T1) (y : @?T2 x) (z : @?T3 x y), @?f x y z =>
      uncurry (fun xyz => H (Common_projT1 (Common_projT1 xyz)) (Common_projT2 (Common_projT1 xyz)) (Common_projT2 xyz))
    | forall (x : ?T1) (y : @?T2 x), @?f x y => uncurry (fun xy : @Common_sigT T1 T2 => H (Common_projT1 xy) (Common_projT2 xy))
    | ?H' => H
  end.

Ltac curry H := let HT := type of H in
  match eval simpl in HT with
    | forall xy : @Common_sigT ?T1 ?T2, @?f xy => curry (fun (x : T1) (y : T2 x) => H (@Common_existT T1 T2 x y))
    | ?H' => H
  end.

Lemma fg_equal A B (f g : A -> B) : f = g -> forall x, f x = g x.
  intros; repeat subst; reflexivity.
Qed.

Section telescope.
  Inductive telescope :=
  | Base : forall (A : Type) (B : A -> Type), (forall a, B a) -> (forall a, B a) -> telescope
  | Quant : forall A : Type, (A -> telescope) -> telescope.

  Fixpoint telescopeOut (t : telescope) :=
    match t with
      | Base _ _ x y => x = y
      | Quant _ f => forall x, telescopeOut (f x)
    end.

  Fixpoint telescopeOut' (t : telescope) :=
    match t with
      | Base _ _ f g => forall x, f x = g x
      | Quant _ f => forall x, telescopeOut' (f x)
    end.

  Theorem generalized_fg_equal : forall (t : telescope),
    telescopeOut t
    -> telescopeOut' t.
    induction t; simpl; intuition; subst; auto.
  Qed.
End telescope.

Ltac curry_in_Quant H :=
  match eval simpl in H with
    | @Quant (@Common_sigT ?T1 ?T2) (fun xy => @?f xy) => curry_in_Quant (@Quant T1 (fun x => @Quant (T2 x) (fun y => f (@Common_existT T1 T2 x y))))
    | ?H' => H'
  end.

Ltac reifyToTelescope' H := let HT := type of H in let H' := uncurryT HT in
  match H' with
    | @eq ?T ?f ?g => let T' := eval hnf in T in
      match T' with
        | forall x : ?a, @?b x => constr:(@Base a b f g)
      end
    | forall x, @eq (@?T x) (@?f x) (@?g x) => let T' := eval hnf in T in (* XXX does [hnf] even do anything on [(fun _ => _)]?  I want to do [hnf] inside the function, but I don't want to do [compute] *)
      match T' with
        | (fun x => forall y : @?a x, @?b x y) => constr:(Quant (fun x => @Base (a x) (b x) (f x) (g x)))
      end
  end.

Ltac reifyToTelescope H := let t' := reifyToTelescope' H in curry_in_Quant t'.
Ltac fg_equal_in H := let t := reifyToTelescope H in apply (generalized_fg_equal t) in H; simpl in H.

Ltac fg_equal :=
  repeat match goal with
           | [ H : _ |- _ ] => fg_equal_in H
         end.

Lemma f_equal_helper A0 (A B : A0 -> Type) (f : forall a0, A a0 -> B a0) (x y : forall a0, A a0) :
  (forall a0, x a0 = y a0) -> (forall a0, f a0 (x a0) = f a0 (y a0)).
  intros H a0; specialize (H a0); rewrite H; reflexivity.
Qed.

Ltac f_equal_in_r H k := let H' := uncurry H in let H'T := type of H' in
  let k' := (fun v => let v' := curry v in let H := fresh in assert (H := v'); simpl in H) in
    match eval simpl in H'T with
      | @eq ?A ?x ?y => k (fun B (f : A -> B) => @f_equal A B f x y H') k'
      | forall a0 : ?A0, @eq (@?A a0) (@?x a0) (@?y a0)
        => k (fun (B : A0 -> Type) (f : forall a0 : A0, A a0 -> B a0) => @f_equal_helper A0 A B f x y H') k'
    end; clear H.
Ltac f_equal_in f H := f_equal_in_r H ltac:(fun pf k => k (pf _ f)).

Ltac eta_red :=
  repeat match goal with
           | [ H : appcontext[fun x => ?f x] |- _ ] => change (fun x => f x) with f in H
           | [ |- appcontext[fun x => ?f x] ] => change (fun x => f x) with f
         end.

Lemma sigT_eta : forall A (P : A -> Type) (x : sigT P),
  x = existT _ (projT1 x) (projT2 x).
  destruct x; reflexivity.
Qed.

Lemma sigT2_eta : forall A (P Q : A -> Type) (x : sigT2 P Q),
  x = existT2 _ _ (projT1 x) (projT2 x) (projT3 x).
  destruct x; reflexivity.
Qed.

Lemma sig_eta : forall A (P : A -> Prop) (x : sig P),
  x = exist _ (proj1_sig x) (proj2_sig x).
  destruct x; reflexivity.
Qed.

Lemma sig2_eta : forall A (P Q : A -> Prop) (x : sig2 P Q),
  x = exist2 _ _ (proj1_sig x) (proj2_sig x) (proj3_sig x).
  destruct x; reflexivity.
Qed.

Lemma prod_eta : forall (A B : Type) (x : A * B),
  x = pair (fst x) (snd x).
  destruct x; reflexivity.
Qed.

Ltac rewrite_eta_in Hf :=
  repeat match type of Hf with
           | context[match ?E with existT2 _ _ _ => _ end] => rewrite (sigT2_eta E) in Hf; simpl in Hf
           | context[match ?E with exist2 _ _ _ => _ end] => rewrite (sig2_eta E) in Hf; simpl in Hf
           | context[match ?E with existT _ _ => _ end] => rewrite (sigT_eta E) in Hf; simpl in Hf
           | context[match ?E with exist _ _ => _ end] => rewrite (sig_eta E) in Hf; simpl in Hf
           | context[match ?E with pair _ _ => _ end] => rewrite (prod_eta E) in Hf; simpl in Hf
         end.

Ltac rewrite_eta :=
  repeat match goal with
           | [ |- context[match ?E with existT2 _ _ _ => _ end] ] => rewrite (sigT2_eta E); simpl
           | [ |- context[match ?E with exist2 _ _ _ => _ end] ] => rewrite (sig2_eta E); simpl
           | [ |- context[match ?E with existT _ _ => _ end] ] => rewrite (sigT_eta E); simpl
           | [ |- context[match ?E with exist _ _ => _ end] ] => rewrite (sig_eta E); simpl
           | [ |- context[match ?E with pair _ _ => _ end] ] => rewrite (prod_eta E); simpl
         end.

Ltac intro_proj2_sig_from_goal'_by tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => tac (proj2_sig x)
           | [ |- appcontext[proj1_sig (sig_of_sig2 ?x)] ] => tac (proj3_sig x)
         end.

Ltac intro_proj2_sig_from_goal_by tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => tac (proj2_sig x)
           | [ |- appcontext[proj1_sig (sig_of_sig2 ?x)] ] => tac (proj3_sig x)
         end; simpl in *.

Ltac intro_projT2_from_goal_by tac :=
  repeat match goal with
           | [ |- appcontext[projT1 ?x] ] => tac (projT2 x)
           | [ |- appcontext[projT1 (sigT_of_sigT2 ?x)] ] => tac (projT3 x)
         end; simpl in *.

Ltac intro_proj2_sig_by tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] => tac (proj2_sig x)
           | [ H : appcontext[proj1_sig ?x] |- _ ] => tac (proj2_sig x)
           | [ H := appcontext[proj1_sig ?x] |- _ ] => tac (proj2_sig x)
           | [ |- appcontext[proj1_sig (sig_of_sig2 ?x)] ] => tac (proj3_sig x)
           | [ H : appcontext[proj1_sig (sig_of_sig2 ?x)] |- _ ] => tac (proj3_sig x)
           | [ H := appcontext[proj1_sig (sig_of_sig2 ?x)] |- _ ] => tac (proj3_sig x)
         end; simpl in *.

Ltac intro_projT2_by tac :=
  repeat match goal with
           | [ |- appcontext[projT1 ?x] ] => tac (projT2 x)
           | [ H : appcontext[projT1 ?x] |- _ ] => tac (projT2 x)
           | [ H := appcontext[projT1 ?x] |- _ ] => tac (projT2 x)
           | [ |- appcontext[projT1 (sigT_of_sigT2 ?x)] ] => tac (projT3 x)
           | [ H : appcontext[projT1 (sigT_of_sigT2 ?x)] |- _ ] => tac (projT3 x)
           | [ H := appcontext[projT1 (sigT_of_sigT2 ?x)] |- _ ] => tac (projT3 x)
         end; simpl in *.


Ltac intro_proj2_sig_from_goal' := intro_proj2_sig_from_goal'_by unique_pose.
Ltac intro_proj2_sig_from_goal := intro_proj2_sig_from_goal_by unique_pose.
Ltac intro_projT2_from_goal := intro_projT2_from_goal_by unique_pose.
Ltac intro_projT2_from_goal_with_body := intro_projT2_from_goal_by unique_pose_with_body.
Ltac intro_proj2_sig := intro_proj2_sig_by unique_pose.
Ltac intro_projT2 := intro_projT2_by unique_pose.
Ltac intro_projT2_with_body := intro_projT2_by unique_pose_with_body.

Ltac recr_destruct_with tac H :=
  let H0 := fresh in let H1 := fresh in
    (tac H; try reflexivity; try clear H) ||
      (destruct H as [ H0 H1 ];
        simpl in H0, H1;
          recr_destruct_with tac H0 || recr_destruct_with tac H1;
            try clear H0; try clear H1).

Ltac do_rewrite H := rewrite H.
Ltac do_rewrite_rev H := rewrite <- H.
Ltac recr_destruct_rewrite H := recr_destruct_with do_rewrite H.
Ltac recr_destruct_rewrite_rev H := recr_destruct_with do_rewrite_rev H.


Ltac use_proj2_sig_with tac :=
  repeat match goal with
           | [ |- appcontext[proj1_sig ?x] ] =>
             match x with
               | context[proj1_sig] => fail 1
               | _ => simpl_do_clear tac (proj2_sig x)
             end
         end.

Ltac rewrite_proj2_sig := use_proj2_sig_with recr_destruct_rewrite.
Ltac rewrite_rev_proj2_sig := use_proj2_sig_with recr_destruct_rewrite_rev.

Definition is_unique (A : Type) (x : A) := forall x' : A, x' = x.
Implicit Arguments is_unique [A].

Ltac rewrite_unique :=
  match goal with
    | [ H : is_unique _ |- _ ] => unfold is_unique in H; rewrite H || rewrite <- H; reflexivity
  end.

Ltac generalize_is_unique_hyp H T :=
  assert (forall a b : T, a = b) by (intros; etransitivity; apply H || symmetry; apply H); clear H.

Ltac generalize_is_unique :=
  repeat match goal with
           | [ H : @is_unique ?T _ |- _ ] => generalize_is_unique_hyp H T
         end.

Ltac intro_fresh_unique :=
  repeat match goal with
           | [ H : @is_unique ?T ?x |- _ ] => let x' := fresh in assert (x' := x); rewrite <- (H x') in *; generalize_is_unique_hyp H T
         end.

Ltac specialize_with_evars_then_do E tac :=
  match type of E with
    | forall x : ?T, _ =>
      let y := fresh in evar (y : T);
        let y' := (eval unfold y in y) in clear y;
          specialize_with_evars_then_do (E y') tac
    | _ => tac E
  end.

Ltac specialize_hyp_with_evars E :=
  repeat match type of E with
           | forall x : ?T, _ =>
             let y := fresh in evar (y : T);
               let y' := (eval unfold y in y) in clear y;
                 specialize (E y')
         end.

(* rewrite fails if hypotheses depend on one another.  simultaneous rewrite does not *)
Ltac simultaneous_rewrite' E :=
  match type of E with
    | ?X = _ => generalize E; generalize dependent X; intros until 1;
      let H := fresh in intro H at top;
        match type of H with
          ?X' = _ => subst X'
        end
  end.

Ltac simultaneous_rewrite_rev' E :=
  match type of E with
    | _ = ?X => generalize E; generalize dependent X; intros until 1;
      let H := fresh in intro H at top;
        match type of H with
          _ = ?X' => subst X'
        end
  end.

Ltac simultaneous_rewrite E := specialize_with_evars_then_do E ltac:(fun E =>
  match type of E with
    | ?T = _ => let H := fresh in
      match goal with
        | [ _ : context[?F] |- _ ] =>
          assert (H : T = F) by reflexivity; clear H
      end; simultaneous_rewrite' E
  end
).

Ltac simultaneous_rewrite_rev E := specialize_with_evars_then_do E ltac:(fun E =>
  match type of E with
    | _ = ?T => let H := fresh in
      match goal with
        | [ _ : context[?F] |- _ ] =>
          assert (H : T = F) by reflexivity; clear H
      end; simultaneous_rewrite_rev' E
  end
).

(* rewrite by convertiblity rather than syntactic equality *)
Ltac conv_rewrite_with rew_tac H := specialize_with_evars_then_do H ltac:(fun H =>
  match type of H with
    | ?a = _ => match goal with
                  | [ |- appcontext[?a'] ] => let H' := fresh in assert (H' : a = a') by reflexivity; clear H';
                    change a' with a; rew_tac H
                end
  end
).
Ltac conv_rewrite_rev_with rew_tac H := specialize_with_evars_then_do H ltac:(fun H =>
  match type of H with
    | _ = ?a => match goal with
                  | [ |- appcontext[?a'] ] => let H' := fresh in assert (H' : a = a') by reflexivity; clear H';
                    change a' with a; rew_tac H
                end
  end
).

Ltac conv_rewrite H := conv_rewrite_with ltac:(fun h => rewrite h) H.
Ltac conv_rewrite_rev H := conv_rewrite_rev_with ltac:(fun h => rewrite <- h) H.
Ltac conv_repeat_rewrite H := repeat conv_rewrite_with ltac:(fun h => repeat rewrite h) H.
Ltac conv_repeat_rewrite_rev H := repeat conv_rewrite_rev_with ltac:(fun h => repeat rewrite <- h) H.

Ltac rewrite_by_context ctx H :=
  match type of H with
    | ?x = ?y => let ctx' := context ctx[x] in let ctx'' := context ctx[y] in
      cut ctx'; [ let H' := fresh in intro H'; simpl in H' |- *; exact H' | ];
        cut ctx''; [ let H' := fresh in intro H'; etransitivity; try apply H'; rewrite H; reflexivity
          |
        ]
  end.

Ltac rewrite_rev_by_context ctx H :=
  match type of H with
    | ?x = ?y => let ctx' := context ctx[y] in let ctx'' := context ctx[x] in
      cut ctx'; [ let H' := fresh in intro H'; simpl in H' |- *; exact H' | ];
        cut ctx''; [ let H' := fresh in intro H'; etransitivity; try apply H'; rewrite <- H; reflexivity
          |
        ]
  end.

Ltac do_for_each_hyp' tac fail_if_seen :=
  match goal with
    | [ H : _ |- _ ] => fail_if_seen H; tac H; try do_for_each_hyp' tac ltac:(fun H' => fail_if_seen H'; match H' with | H => fail 1 | _ => idtac end)
  end.
Ltac do_for_each_hyp tac := do_for_each_hyp' tac ltac:(fun H => idtac).

(* [change a with b in *] fails if it would create a self-referential hypothesis.
   This version does not. *)
Tactic Notation "change_in_all" constr(from) "with" constr(to) :=
  change from with to; do_for_each_hyp ltac:(fun H => change from with to in H).

(* [expand] replaces both terms of an equality (either [eq] or [JMeq]
   in the goal with their head normal forms *)
Ltac expand :=
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

(* [hideProof' pf] generalizes [pf] only if it does not already exist
   as a hypothesis *)
Ltac hideProof' pf :=
  match goal with
    | [ x : _ |- _ ] => match x with
                          | pf => fail 2
                        end
    | _ => generalize pf; intro
  end.

(* TODO(jgross): Is there a better way to do this? *)
Tactic Notation "hideProofs" constr(pf)
  := hideProof' pf.
Tactic Notation "hideProofs" constr(pf0) constr(pf1)
  := progress (try hideProof' pf0; try hideProof' pf1).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4).
Tactic Notation "hideProofs" constr(pf0) constr(pf1) constr(pf2) constr(pf3) constr(pf4) constr(pf5)
  := progress (try hideProof' pf0; try hideProof' pf1; try hideProof' pf2; try hideProof' pf3; try hideProof' pf4; try hideProof' pf5).

Ltac destruct_to_empty_set :=
  match goal with
    | [ H : Empty_set |- _ ] => destruct H
    | [ H : ?T -> Empty_set, a : ?T |- _ ] => destruct (H a)
    | [ H : context[Empty_set] |- _ ] => solve [ destruct H; trivial; assumption ]
  end.

Ltac destruct_to_empty_set_in_match :=
  match goal with
    | [ |- appcontext[match ?x with end] ] => solve [ destruct x || let H := fresh in pose x as H; destruct H ]
    | [ _ : appcontext[match ?x with end] |- _ ] => solve [ destruct x || let H := fresh in pose x as H; destruct H ]
  end.

Section unit.
  Lemma unit_singleton (u : unit) : u = tt.
    case u; reflexivity.
  Qed.

  Lemma unit_eq (u u' : unit) : u = u'.
    case u; case u'; reflexivity.
  Qed.

  Lemma unit_JMeq (u u' : unit) : u == u'.
    case u; case u'; reflexivity.
  Qed.

  Lemma Empty_set_eq (a b : Empty_set) : a = b.
    destruct a.
  Qed.

  Lemma Empty_set_JMeql (a : Empty_set) T (b : T) : a == b.
    destruct a.
  Qed.

  Lemma Empty_set_JMeqr T (a : T) (b : Empty_set) : a == b.
    destruct b.
  Qed.
End unit.

Hint Rewrite unit_singleton.
Hint Extern 0 (@eq unit _ _) => apply unit_eq.
Hint Extern 0 (@JMeq unit _ unit _) => apply unit_JMeq.
Hint Extern 0 unit => constructor.
Hint Extern 0 (@eq Empty_set _ _) => apply Empty_set_eq.
Hint Extern 0 (@JMeq Empty_set _ _ _) => apply Empty_set_JMeql.
Hint Extern 0 (@JMeq _ _ Empty_set _) => apply Empty_set_JMeqr.
