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

Definition ival_event_prec : event_ival -> event -> Prop :=
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
#[local] Notation thread_event_ival := (event_ival thread_event_occ).
#[local] Notation thread_event_ival_prec := (event_ival_prec thread_event_occ).

#[export] Instance thread_event_prec_strict_order : StrictOrder thread_event_prec.
Proof. typeclasses eauto. Qed.
#[export] Instance thread_event_prec_trichotomy : Trichotomy (strict thread_event_prec).
Proof. apply event_prec_trichotomy, thread_event_occ_simul. Qed.

Section LockOne.
Variables (A B : thread).
Hypothesis A_neq_B : A <> B.

Definition A_write_flag_A_true : thread * string := (A, "write(flag[A],true)").
Definition B_write_flag_B_true : thread * string := (B, "write(flag[B],true)").
Definition A_read_flag_B_false : thread * string := (A, "read(flag[B],false)").
Definition B_read_flag_A_false : thread * string := (B, "read(flag[A],false)").
Definition A_CS : thread * string := (A, "CS").
Definition B_CS : thread * string := (B, "CS").

(* directly from code *)
Hypothesis A_write_A_prec_read_A :
 thread_event_prec A_write_flag_A_true A_read_flag_A_true.
Hypothesis A_read_A_prec_CS :
 thread_event_prec A_read_flag_A_true A_CS.
Hypothesis B_write_B_prec_read_B :
 thread_event_prec B_write_flag_B_true B_read_flag_B_true.
Hypothesis B_read_B_prec_CS :
 thread_event_prec B_read_flag_B_true B_CS.

(* derived from facts in code *)
Lemma A_write_flag_A_true_prec_A_CS :
 thread_event_prec A_write_flag_A_true A_CS.
Proof. eapply StrictOrder_Transitive; eauto. Qed.

Lemma B_write_flag_true_B_prec_B_CS :
 thread_event_prec B_write_flag_B_true B_CS.
Proof. eapply StrictOrder_Transitive; eauto. Qed.

Hypothesis A_read_flag_B_false

End LockOne.

End ThreadStringEvents.
