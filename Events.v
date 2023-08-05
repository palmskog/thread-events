From stdpp Require Import prelude strings.

Section Events.

Context `{EqDecision event}.

Variable event_occ : event -> nat.

Hypothesis event_occ_simul :
 forall e e' : event, event_occ e = event_occ e' -> e = e'.

Definition event_prec : relation event :=
 fun e e' => event_occ e < event_occ e'.

Definition event_ival : Type := { ee | event_prec ee.1 ee.2 }.

Definition ival_prec : relation event_ival :=
 fun iv iv' => event_prec (proj1_sig iv).2 (proj1_sig iv').1.

Definition event_ival_prec : event -> event_ival -> Prop :=
 fun e iv => event_prec e (proj1_sig iv).1.

Definition ival_even_prec : event_ival -> event -> Prop :=
 fun iv e => event_prec (proj1_sig iv).2 e.

#[export] Instance event_prec_strict_order : StrictOrder event_prec.
Proof.
split.
- by intros x; unfold complement, event_prec; lia.
- by intros x y z; unfold event_prec; lia.
Qed.

#[export] Instance event_prec_trichotomy : Trichotomy (strict event_prec).
Proof.
intros x y; unfold strict, event_prec.
destruct (decide (event_occ x < event_occ y)).
- by left; lia.
- destruct (decide (event_occ x = event_occ y)).
  * by apply event_occ_simul in e; right; left.
  * by right; right; lia.
Qed.

#[export] Instance ival_prec_strict_order : StrictOrder ival_prec.
Proof.
split.
- intros x; unfold complement, ival_prec.
  destruct x; destruct x; simpl in *.
  by unfold event_prec in *; lia.
- intros x y z; unfold ival_prec.
  destruct x; destruct x.
  destruct y; destruct x.
  destruct z; destruct x; simpl in *.
  intros He1 He4.
  unfold event_prec in *.
  by lia.
Qed.

#[export] Instance ival_prec_antisymm : AntiSymm eq ival_prec.
Proof.
intros x y Hx Hy; unfold ival_prec in *.
destruct x; destruct x.
destruct y; destruct x.
simpl in *.
unfold event_prec in *.
by lia.
Qed.

End Events.

Section ThreadStringEvents.

Context `{EqDecision thread}.

Variable thread_event_occ : thread * string -> nat.

Hypothesis thread_event_occ_simul :
 forall e e' : thread * string,
  thread_event_occ e = thread_event_occ e' -> e = e'.

#[local] Notation thread_event_prec := (event_prec thread_event_occ).

End ThreadStringEvents.
