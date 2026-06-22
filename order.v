From HB Require Import structures.
From mathcomp Require Import all_ssreflect perm fingroup.

From PG2X Require Import projective_plane_axioms_alt.

(*
Record incid_struct := {
  point : finType;
  line:finType;
  incid:point->line->bool}.

Definition is_pp (i : incid_struct) :=
forall (A B : point i) , exists l : line i,  incid i A l /\ incid i B l /\ 
forall (l1 l2 : line i), exists A : point i, incid i A l1 /\ incid i A l2 /\ 
forall (A B : point i)(l1 l2 : line i),
  incid i A l1 -> incid i B l1  -> incid i A l2 -> incid i B l2 -> A == B \/ l1 == l2 /\ 
exists A : point i, exists  B : point i, exists C : point i, exists D : point i,
  forall l : line i, A != B /\ A !=C /\ A != D /\ B != C /\ B !=D /\ C!= D
  /\ (incid i A l /\ incid i B l -> ~incid i C l /\ ~incid i D l)
  /\ (incid i A l /\ incid i C l -> ~incid i B l /\ ~incid i D l)
  /\ (incid i A l /\ incid i D l -> ~incid i C l /\ ~incid i B l)
  /\ (incid i C l /\ incid i B l -> ~incid i A l /\ ~incid i D l)
  /\ (incid i D l /\ incid i B l -> ~incid i C l /\ ~incid i A l)
  /\ (incid i C l /\ incid i D l -> ~incid i B l /\ ~incid i A l).
*)

Section order.

Context
  {point : finType}
  {line : finType}
  {incid : point -> line -> bool}
  {PP : ProjectivePlane point line incid}.

Definition P (l:line) : finType:= {p:point | incid p l}.
Definition L  (p:point) : finType:= {l:line | incid p l}.

Lemma embed :  forall l A B HA HB, A <>B -> exist (fun x : point => incid x l) A HA !=  exist (fun x : point => incid x l) B HB.
Proof.
move => l A B HA HB /eqP HAB.
apply/eqP.
intro Hex.
inversion Hex.
rewrite H0 in HAB.
by rewrite eq_refl in HAB.
Qed.

Lemma at_least_3_points_per_line : forall (l:line), 3 <= #| P l |.
Proof.
  move => l.
  case: (a3_1 l) => A [B [C [Huniq' [ HA  [ HB HC ]]]]]. 
  have hle : size[:: A; B; C] <= #|P l|.
  apply/card_geqP.
  pose pA := @exist  point (fun x => incid x l) A HA.
  pose pB := @exist  point (fun x => incid x l) B HB.
  pose pC := @exist  point (fun x => incid x l) C HC.
  assert (uniq [::pA;pB;pC]).
  destruct Huniq' as [HAB [HAC HBC]].
  assert (pA!=pB).
  apply embed; assumption.
  assert (pA!=pC).
  apply embed; assumption.
  assert (pB!=pC).
  apply embed; assumption.
  apply/and3P; split.
  rewrite !inE.
  apply/norP.
  split.
  assumption.
  assumption.
  rewrite !inE.
  assumption.
  by [].
 exists [::pA;pB;pC]; by apply And3.
 by rewrite /= in hle.
Qed.

Lemma x1_x2_x3_l : forall (l:line),  exists x1, exists x2, exists x3, uniq[::x1;x2;x3] && incid x1 l && incid x2 l && incid x3 l.
Proof.
intros.
destruct (a3_1 l) as [ A [ B [ C [Hdist [HA [HB HC ]]]]]].
unfold dist3 in Hdist.
exists A;exists B; exists C.
apply/andP.
split; [ | assumption].
apply/andP.
split; [ | assumption].
apply/andP.
split; [ | assumption].
rewrite /= !inE.
apply/andP.
  split.
apply/norP.
split.
apply/eqP; tauto.
apply/eqP; tauto.
apply/andP.
split.
apply/eqP; tauto.
by [].
Qed.

Lemma at_least_3_lines_per_point : forall  (p:point), 3 <= #| L p |.
Admitted.

Lemma x_l1_l2_l3 : forall (x:point),  exists l1, exists l2, exists l3, uniq[::l1;l2;l3] && incid x l1 && incid x l2 && incid x l3.
Proof.
Admitted.


Lemma one_line_outside_P : forall  (p:point), {l:line | ~ incid p l}.
Proof.
Admitted.
(*
Lemma one_line_outside_P' : forall (p:point), {l:line | ~~ (p \in P l)}.
Proof.
Admitted.
*)

Lemma order_def : 
  {n:nat |  (2 <= n) && [forall l:line, #| P l | == n.+1] && [forall p:point, #| L p | == n.+1]}.
Proof.
destruct (seven_lines) as [l [l' [l3 [l4 [l5 [l6 [l7 Huniq]]]]]]].
destruct (a2_exist l l') as [p [Hpl Hpl']].
assert (Hl'':{l'':line | incid p l'' && uniq [::l;l';l'']}).
admit.
destruct Hl'' as [l'' Hl''].
assert (Hp':{p':point | incid p' l'' && uniq [::p;p']}).
admit.


Admitted.

Definition order : nat := proj1_sig order_def.

(* to be fixed *)
Lemma order_unique :  forall n m:nat, order == n -> order  == m -> n==m.
Proof.
 move =>  n m /eqP Hn /eqP Hm.
 apply/eqP. 
 rewrite <- Hn; rewrite <- Hm; reflexivity.
Qed.

Lemma order_points_lines : forall (n:nat) (Ho:order == n), (#| point | == n*n+n+1) && (#| point | == #| line |).
Proof.
  move => n Ho.
  apply/andP. 
  split.
Admitted.

End order.



