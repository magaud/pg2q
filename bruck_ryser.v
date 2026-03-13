From HB Require Import structures.
From mathcomp Require Import all_ssreflect perm fingroup.
From PG2X Require Import projective_plane_axioms_alt order incid_mats.
From Stdlib Require Import Arith. 

Section bruck_ryser.

Context
  {point : finType}
  {line : finType}
  {incid : point -> line -> bool}
  {PP : ProjectivePlane point line incid}.

Theorem bruck_ryser : 
  forall (n:nat), ( order = n) -> Nat.modulo n 4 = 1 \/ Nat.modulo n 4 = 2 -> 
exists p:nat, exists q:nat, (n = p * p + q * q)%nat.
Proof.
Admitted.


Lemma bruck_ryser' : forall n:nat, (order = n) -> (Nat.modulo n 4 = 1 \/ Nat.modulo n 4 = 2) -> 
(forall p q:nat, n != p * p + q * q) -> False. (*~exists i:incid_struct, is_pp i /\ (forall H:(is_pp i), order i H=n).*)
Proof.
intros n Ho Hmod Hsum.
destruct (bruck_ryser n Ho Hmod) as [p [q Hpq]].
generalize (Hsum p q); clear Hsum; intros Hsum.
rewrite <- Hpq in Hsum.
by rewrite eqxx in Hsum.
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

