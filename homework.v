From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* A bit of logic to master your SSReflect skills :) *)

Section Logic.

Variables P Q R : Prop.

Lemma or_and_distr :
  (P \/ Q) /\ R -> P /\ R \/ Q /\ R.
Proof.
Admitted.

Lemma contraposition :
  (P -> ~ Q) -> (Q -> ~ P).
Proof.
Admitted.

Lemma p_is_not_equal_not_p :
  ~ (P <-> ~ P).
Proof.
Admitted.

Lemma weak_Peirce :
  ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
Admitted.

Lemma curry_dep A (S : A -> Prop) :
  ((exists x, S x) -> Q) -> (forall x, S x -> Q).
Proof.
Admitted.


Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Lemma lem_implies_Frobenius2 : LEM -> Frobenius2.
Proof.
Admitted.

Lemma Frobenius2_lem : Frobenius2 -> LEM.
Proof.
Admitted.


End Logic.
