From Coqtail Require Import Arith.Lagrange_four_square.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect  all_algebra perm fingroup.
From PG2X Require Import projective_plane_axioms_alt order incid_mats lemmas rationals.
From Stdlib Require Import Arith. 

Open Scope ring_scope.

Section bruck_ryser.

Context
  {point : finType}
  {line : finType}
  {incid : point -> line -> bool}
  {PP : ProjectivePlane point line incid}.

Lemma order_matrix : forall n:nat, (order =n) ->
forall m:nat, m=n*n+n+1 -> 
  exists M:'M[rat]_(m,m), 
    M*m M^T = n%:R + \matrix_(i<m, j<m) 1.
Proof.
Admitted.


Theorem bruck_ryser : 
  forall (n:nat), ( order = n) -> Nat.modulo n 4 = 1%nat \/ Nat.modulo n 4 = 2 -> 
exists p:nat, exists q:nat, (n = p * p + q * q)%nat.
Proof.
intros.
pose m:=n*n+n+1.
destruct (order_matrix n H m) as [A HA].
by [].
destruct (Lagrange n) as [a [b [c [d Habcd]]]].


pose B : 'M[rat]_(4,4) :=
  \matrix_(i < 4, j < 4)
     match (nat_of_ord i, nat_of_ord j) with
     | (0%nat,0%nat) => a%:R | (0%nat,1%nat) => -b%:R | (0%nat,2%nat) => -c%:R | (0%nat,3%nat) => -d%:R
     | (1%nat,0%nat) => b%:R | (1%nat,1%nat) => a%:R | (1%nat,2%nat) => d%:R | (1%nat,3%nat) => -c%:R
     | (2%nat,0%nat) => c%:R | (2%nat,1%nat) => -d%:R | (2%nat,2%nat) => a%:R | (2%nat,3%nat) => b%:R
     | (3%nat,0%nat) => d%:R | (3%nat,1%nat) => c%:R | (3%nat,2%nat) => -b%:R | (_,_) => a%:R
     end.
assert (\det B <>0) by admit.
pose B_1 := invmx B.
Check castmx.
assert (Heq:(\sum_(i<(m.+1/4)) 4 = (m+1))) by admit.
pose B' : 'M[rat]_(m+1,m+1) := castmx (Heq,Heq) (\mxdiag_(i < (m.+1)/4)  B_1).
Check B'.
pose A' := col_mx (row_mx A (\col_(j<m) 0%:R)) (\row_(i<m+1) (if (i==m :> nat) then 1 else 0)).
Check A'.

pose C :'M[rat]_(m+1,1):= (\col_(i<m+1) (if (i==m :> nat) then 0 else 1)).
Check C.

Check B'.
assert (Heq1:(m+1=m.+1)) by by rewrite -addn1.
assert (Heq2:(m+1+1=m.+2)) by by rewrite -addn1 -addn1.

pose M:= castmx (Heq1,Heq2) (row_mx (B' *m A') (B' *m C)).
Check M.

Check technical_lemma.
assert ((forall z:'rV[rat]_(m.+2), 

forall y:'rV[rat]_(m.+1),
(z = y*m M) -> \sum_(i<m) (z 0 (inord i) )*(z 0  (inord i)) + n%:R*(z 0 (inord m))*(z 0 (inord m)) = \sum_(i<m.+1) (y 0 i )*(y 0  i ) + (z 0 (inord (m.+1)))*(z 0 (inord (m.+1))))).
admit.

assert (Hn:n<>0) by admit.
assert (Hm:m<>0) by admit.
destruct (technical_lemma n m Hn Hm M) as [y Hy].
admit.
pose z:= y *m M. 
assert (z = y *m M).
reflexivity.
generalize (Hy z H3); intros [Hy1 Hy2].
pose (m1 := (denq (z 0 (inord m)))).
pose (m2 := denq (y 0 (inord m))).
pose (m3 := denq (z 0 (inord m.+1))).
(*
assert ((m1* m1* m2* m2* m3* m3*(n%:R * z 0 (inord m) * z 0 (inord m)))%:R = 
y 0 (inord m) * (y 0 (inord m) + z 0 (inord m.+1) * z 0 (inord m.+1))).

*)
Check B.
Admitted.


Lemma bruck_ryser' : forall n:nat, (order = n) -> (Nat.modulo n 4 = 1%nat \/ Nat.modulo n 4 = 2) -> 
(forall p q:nat, n != p * p + q * q) -> False. (*~exists i:incid_struct, is_pp i /\ (forall H:(is_pp i), order i H=n).*)
Proof.
intros n Ho Hmod Hsum.
destruct (bruck_ryser n Ho Hmod) as [p [q Hpq]].
generalize (Hsum p q); clear Hsum; intros Hsum.
by rewrite Hpq eqxx in Hsum.
Qed.

Lemma foo_bar_6 : forall p q:nat, 6<> p * p + q * q.
Proof.
intros; intro.

destruct p.
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.

destruct p.
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.
-
destruct p.
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.

cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.
Qed.

Lemma foo_6 :  forall p q:nat, 6 != p * p + q * q.
Proof.
intros; apply/eqP.
apply foo_bar_6.
Qed.

Lemma no_plane_exists_when_n_is_6 : order = 6 -> False. (*~exists i:incid_struct, is_pp i /\ forall H:is_pp i, order i H = 6.*)
Proof.
intros.
apply bruck_ryser' with (n:=6).
assumption.
subst; right; reflexivity.
apply foo_6.
Qed.

Lemma foo_bar_14 : forall p q:nat, 14<> p * p + q * q.
Proof.
intros; intro.

destruct p.
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.

destruct p.
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.

destruct p.
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.

destruct p.
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
destruct q; [ discriminate | idtac].
cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.


cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; cbv in H; repeat rewrite <- Nat.add_succ_comm in H; discriminate.
Qed.

Lemma foo_14 :  forall p q:nat, 14 != p * p + q * q.
Proof.
intros; apply/eqP.
apply foo_bar_14.
Qed.

Lemma no_plane_exists_when_n_is_14 :  order = 14 -> False. (*~exists i:incid_struct, is_pp i /\ forall H:is_pp i, order i H = 14.*)
Proof.
intros.
apply bruck_ryser' with (n:=14).
assumption.
subst; right; reflexivity.
apply foo_14.
Qed.

(* 2.2.1 proves that there exists a finite projective plane of order n whether n is a prime power *)

(* 3.3.1 Bruck-Ryser rules out several other open cases *)
(* orders not ruled out by 3.3.1 are 10, 12, 15, 18, 20, 24, 26, 28, 34, 35, 36, 39, 40, 44, 45, 48, 50, 51, 52, 55, 56, 58, 60, 63, 65, 68, 72, 74, 75, 76, 80, 82, 84, 85, 87, 88, 90, 91, 92, 95, 96, 98, 99 and 100 *)

End bruck_ryser.
