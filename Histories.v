From stdpp Require Import prelude strings.

Section Histories.

Context `{!EqDecision thread}.
Context `{!EqDecision object, !EqDecision method}.
Context `{!EqDecision argument, !EqDecision result, !EqDecision exception}.

Inductive res :=
| res_OK : res
| res_exception : exception -> res.

Record invocation := {
 invoc_object : object;
 invoc_method : method;
 invoc_args : list argument;
}.

Record response := {
 resp_object : object;
 resp_res : res;
 resp_results : list result
}.

Definition H :=
 list (thread * (invocation + response)).

Definition invoc_resp_match (i : invocation) (r : response) : Prop :=
 invoc_object i = resp_object r.

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

Print inr.

Definition method_call : Type := invocation * (option response).

Fixpoint invocation_response (t : thread) (i : invocation) (h : H) : option response :=
match h with
| (t', inr r) :: h' =>
  if decide (t' = t /\ invoc_resp_match i r) then Some r
  else invocation_response t i h'
| (_, _) :: h' => invocation_response t i h'
| [] => None
end.

(* dangling responses are ruled out at generation time *)
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

Definition pending_invocation (h : H) (i : invocation) : Prop :=
 exists t, (t, inl i) ∈ h.
 
Definition pending_method_call (h : H) (mc : method_call) : Prop :=
 pending_invocation h mc.1.

Definition thread_subhistory (h : H) (t : thread) :=
 filter (fun '(t', ev) => t = t') h.

Definition event_object (ev : invocation + response) : object :=
match ev with
| inl i => invoc_object i
| inr r => resp_object r
end.

Definition object_subhistory (h : H) (o : object) :=
 filter (fun '(t', ev) => event_object ev = o) h.

Definition equivalent_history (h h' : H) : Prop :=
 forall (t : thread), thread_subhistory h t = thread_subhistory h' t.

Fixpoint sequential_history (h : H) : Prop :=
match h with
| (t, inl i) :: (t', inr r) :: h' =>
  t = t' /\ invoc_resp_match i r /\ sequential_history h'
| (t, inl i) :: [] => True
| _ => False
end.

Section Legal.

Variable legal_sequential_history : object -> list (invocation + response) -> Prop.
Context `{forall o l, Decision (legal_sequential_history o l)}.

End Legal.

End Histories.
