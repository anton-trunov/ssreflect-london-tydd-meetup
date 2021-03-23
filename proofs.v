From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*|
Basic SSReflect tactics and tacticals
-------------------------------------
|*)

Section Logic.

Context (A B C : Prop).

(*|
The `apply` tactic, `=>` and `:` tacticals
==========================================
|*)

(*| SSReflect's `apply` tactic means

.. code-block:: Coq

   intro top;
   first [refine top |
          refine (top _) |
          refine (top _ _) | …];
   clear top.

Let's see some examples of how this works.
|*)

Goal A -> A.
Proof.
apply.
Qed.

(*| For the next example we are going to need some
"bookkeeping" tacticals:

- the `=>` tactical moves hypotheses from the goal
to the context;

- the `:` tactical moves hypotheses from the
context to the goal;

and also the `move` tactic which can be thought of
as a no-op tactic for now. |*)

Goal A -> (A -> B) -> B.
Proof.
move=> a.
apply. (* generates one subgoal *)
move: a.
apply.
Qed.

Goal A -> B -> (A -> B -> C) -> C.
Proof.
(* we can move several assumptions into
the context at once: *)
move=> a b.
apply.  (* generates two subgoals *)
(* notice the indentation style here *)
- move: a.
  apply.
move: b.
apply.
Qed.

(*|
Interpreting assumptions: `/view`
=================================
|*)
Goal (A -> B) -> A -> C -> B.
Proof.
move=> ab a.
move: (ab a).
(* the rest of the proof is trivial and can be
finished with `done` tactic *)
done.

Restart.
(* But the pattern above is quite common so there
is a shorthand for interpreting assumptions:
`/view` *)
move=> ab.
move=> /ab.

(* The tactics above can be combined into
`move=> ab /ab`.

But here is a recent addition to the view
mechanism: `[apply]` view which looks a bit
differently because it's actually a notation
hiding some Ltac code which is now allowed in
views. *)

Restart.
move/[apply].
done.

(* Or, more concisely: `by move/[apply].`.
Here, we've used the `by` tactical which works a
bit like `done` executed after a tactic. *)
Qed.

(*| The `by` tactical takes a list of tactics (or
a single tactic), applies it to the goal and then
tries to finish the proof using some simple proof
automation. E.g. `by []` means "the proof of the
goal is trivial", because Coq does not need any
hints from the user. This is equivalent to using
the `done` tactic.

The tactics/tacticals `by`, `exact` and `done` are
called "terminators" because if these do not solve
the goal completely, the user gets an error
message. It is advised to put the terminators to
mark where the current subgoal is proven
completely. This helps fixing proofs when they
break, for instance, due to changes in the
definitions of the formalization. |*)


Goal (A -> B) -> (B -> C) -> A -> C.
Proof.
move=> ab ? /ab.

Restart.
(* Or, sometimes we might want to move an
assumption to the context just temporarily: *)
move=> ab + /ab.
done.

(* Btw, if you are a fan of providing proof terms
explicitlty, then you can do it like so: *)
Restart.
exact: catcomp.
Qed.


(*| Specializing assumptions: |*)
Goal A -> (A -> B) -> B.
Proof.
move=> a.
move/(_ a).
apply.

Restart.
by move=> a /(_ a).
Qed.

(*| The `//` tactical: prove trivial goals
automatically. |*)
Lemma HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> abc ab ?.
apply: abc=> //.
(* `=>` serves here as a 'and then do this'
connector *)
by apply: ab.

Restart.
(* Here is a, perhaps, weird proof using the
`/[dup]` view lemma which duplicated the top
assumption. *)
by move=> abc ab /[dup] /ab b /abc /(_ b).
Qed.


(*|
Case analysis
=============
|*)
Goal A /\ B -> A.
Proof.
case.
Undo.
by case.
Qed.

Context (T : Type).
Context (P : T -> Prop).
Implicit Types x y z : T.

Goal ~(exists x, P x) -> forall x, ~P x.
Proof.
by move=> ne x px; apply: ne; eexists; apply: px.
Qed.

Goal (exists x, A -> P x) -> (forall x, ~P x) -> ~A.
Proof.
by case=> x apx npx /apx/npx.
Qed.

(*| A special case for `case`: it handles
injectivity of constructors: |*)
Goal forall x y, (x, y) = (y, x) -> True.
move=> x y.
case.
(* this turns an equality on pairs into a "pair"
of equalities *)
Abort.

(* An example with natural numbers: *)
Goal forall n m,
  n.+1 = m.+1 -> n = m.
Proof.
move=> n m.
case.
done.
Qed.



(*| The `[]` tactical to do case-analysis in-place
|*)
Goal (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
by move=> [ [a | b] c ]; [left | right].
Qed.


(*|
Interpreting goals: `apply/`
============================
|*)
Goal (A -> B) -> B.
move=> ab.
apply/ab. (* interpret the goal with `ab` *)
(* Here it does not look like much, especially
considering we could do that with `apply: ab.`.
Interpretation of assumptions or goals can use a
powerful mechanism called 'view hints' which we
will explore after we talk about
`reflect`-predicates. *)
Abort.


(*|
The `rewrite` tactic
====================
|*)

(*| SSReflect overloads the `rewrite` tactic. And
augments it with a powerful pattern language to
select a place in your goal to perform rewriting.

It's much more powerful than the vanilla `rewrite`
tactic, however, if you ever need to use the
vanilla version you can do it but using the
`rewrite -> equation` or `rewrite <- equation`
syntax. |*)

Goal forall x y, x = y -> y = x.
Proof.
move=> x y x_eq_y.
(* `-` means 'rewrite from right to left' *)
rewrite -x_eq_y.
by [].

Restart.
(* we can make it shorter by using the `->` (or `<-)
intro-pattern. *)
by move=> ?? ->.
Qed.

(*| `move=>->` corresponds to something like this
`move=> fresh; rewrite {}fresh`, where `rewrite
{}eq` means rewrite with `eq` equation and clear
it from the context. |*)

End Logic.


(*|
Induction
=========
|*)

Goal associative addn.
Proof.
move=> x y z.
elim: x=> // x IHx.
(* reduction for addn is blocked, so we have to
use `rewrite`: *)
rewrite !addSn.
(* `!` means 'one or more rewrites' *)
by rewrite IHx.
Qed.

Lemma addnC :
  commutative addn.
Proof.
move=> x y.
elim: x=> [| x IHx]; first by rewrite addn0.
(* `first` tactical lets us to not focus on
trivial goals |*)
by rewrite addSn IHx -addSnnS.
Qed.
