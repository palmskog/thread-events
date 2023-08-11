From stdpp Require Import prelude strings.

Section Histories.

Context `{!EqDecision thread, !EqDecision object, !EqDecision method}.
Context `{!EqDecision argument, !EqDecision result, !EqDecision exception}.

Inductive res :=
| res_OK : res
| res_exception : exception -> res.

Record invocation := {
 invoc_object : object;
 invoc_method : method;
 invoc_args : list argument;
}.

Definition thread_invocation : Type := thread * invocation.

Record response := {
 resp_object : object;
 resp_res : res;
 resp_results : list result
}.

Definition thread_response : Type := thread * response.

Definition event : Type := thread_invocation + thread_response.

Definition H : Type := list event.

Definition invoc_resp_match
 (i : invocation) (r : response) : Prop :=
 invoc_object i = resp_object r.

Definition thread_invoc_resp_match
 (ti : thread_invocation) (tr : thread_response) : Prop :=
 ti.1 = tr.1 /\ invoc_resp_match ti.2 tr.2.

#[export] Instance list_argument_eq_dec : EqDecision (list argument).
Proof. typeclasses eauto. Qed.

#[export] Instance list_result_eq_dec : EqDecision (list result).
Proof. typeclasses eauto. Qed.

#[export] Instance invocation_eq_dec : EqDecision invocation.
Proof.
intros x y; unfold Decision.
decide equality.
- apply list_argument_eq_dec.
- unfold EqDecision, Decision in *; eauto.
- unfold EqDecision, Decision in *; eauto.
Qed.

#[export] Instance res_eq_dec : EqDecision res.
Proof.
unfold EqDecision, Decision; decide equality.
unfold EqDecision, Decision in *; eauto.
Qed.

#[export] Instance response_eq_dec : EqDecision response.
Proof.
intros x y; unfold Decision.
decide equality.
- apply list_result_eq_dec.
- apply res_eq_dec.
- unfold EqDecision, Decision in *; eauto.
Qed.

#[export] Instance invoc_resp_match_dec (i : invocation) (r : response) :
 Decision (invoc_resp_match i r).
Proof.
unfold invoc_resp_match.
typeclasses eauto.
Qed.

#[export] Instance thread_invoc_resp_match_dec
 (ti : thread_invocation) (tr : thread_response) :
 Decision (thread_invoc_resp_match ti tr).
Proof.
unfold thread_invoc_resp_match.
typeclasses eauto.
Qed.

Definition method_call : Type := thread_invocation * (option thread_response).

Fixpoint thread_invocation_response (ti : thread_invocation)
 (h : H) : option thread_response :=
match h with
| inr tr :: h' =>
  if decide (thread_invoc_resp_match ti tr) then Some tr
  else thread_invocation_response ti h'
| _ :: h' => thread_invocation_response ti h'
| [] => None
end.

(* dangling responses are ruled out at generation time *)
(*
Fixpoint complete_invoc (h : H) : H :=
match h with
| (t, inl i) :: h' =>
  match invocation_response t i h' with
  | Some _ => (t, inl i) :: complete_invoc h'
  | None => complete_invoc h'
  end
| ev :: h' => ev :: complete_invoc h'
| [] => []
end.
*)

(* FIXME *)
(*
Definition pending_invocation (h : H) (i : invocation) : Prop :=
 exists t, (t, inl i) ∈ h.
*)
 
(*
Definition pending_method_call (h : H) (mc : method_call) : Prop :=
 pending_invocation h mc.1.
*)

Definition event_thread (ev : event) : thread :=
match ev with
| inl (t,_) => t
| inr (t,_) => t
end.

Definition event_object (ev : event) : object :=
match ev with
| inl (_,i) => invoc_object i
| inr (_,r) => resp_object r
end.

Definition thread_subhistory (h : H) (t : thread) : H :=
 filter (fun ev => event_thread ev = t) h.

Definition object_subhistory (h : H) (o : object) : H :=
 filter (fun ev => event_object ev = o) h.

Definition equivalent_history (h h' : H) : Prop :=
 forall (t : thread), thread_subhistory h t = thread_subhistory h' t.

Fixpoint sequential_history (h : H) : Prop :=
match h with
| inl ti :: inr tr :: h' => thread_invoc_resp_match ti tr /\ sequential_history h'
| inl ti :: [] => True
| [] => True
| _ => False
end.

Fixpoint sequential_invoc_resp (l : list (invocation + response)) : Prop :=
match l with
| inl i :: inr r :: l' => invoc_resp_match i r /\ sequential_invoc_resp l'
| inl i :: [] => True
| [] => True
| _ => False
end.

Section Legal.

Variable sequential_specification : object -> list (invocation + response) -> Prop.
Context `{forall o l, Decision (sequential_specification o l)}.

Hypothesis sequential_specification_sequential_invoc_resp : 
 forall o l, sequential_specification o l -> sequential_invoc_resp l.

Definition event_invocation_response (e : event) : invocation + response :=
match e with
| inl (_,i) => inl i
| inr (_,r) => inr r
end. 

Definition legal_sequential_history (h : H) : Prop :=
  sequential_history h /\
  forall o, sequential_specification o (map event_invocation_response (object_subhistory h o)).

Definition extension (h h' : H) : Prop := True.

Definition complete (h : H) : H := h.

Definition method_call_prec_same (h h' : H) : Prop := True.

Definition linearization (h : H) (s : H) : Prop :=
 legal_sequential_history s /\
 exists h', extension h h' /\
  equivalent_history s (complete h') /\
  method_call_prec_same h s.

Definition linearizable (h : H) : Prop :=
 exists s, linearization h s.

End Legal.

End Histories.
