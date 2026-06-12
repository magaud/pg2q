From Coqtail Require Import Arith.Lagrange_four_square.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect perm fingroup all_algebra ssrZ.
Import GRing.Theory.

From PG2X Require Import incid_mats.
From Stdlib Require Import Arith ZArith Lia.
Locate Nat.modulo.

Lemma mod4_cases :
  forall n,
    Nat.modulo n 4 = 0 \/
    Nat.modulo n 4 = 1 \/
    Nat.modulo n 4 = 2 \/
    Nat.modulo n 4 = 3.
Proof.
  intro n.
  assert (H := Nat.mod_upper_bound n 4).
  destruct (Nat.modulo n 4) as [|[|[|[|r]]]]; solve [intuition].
Qed.

Lemma mod4 : forall n:nat, Nat.modulo n 4 = 1 \/ Nat.modulo n 4 = 2 -> Nat.modulo (n*n+n+1) 4 = 3.
Proof.
Admitted.

(* Theorem 3.1.2 (Lagrange’s four square theorem). *)

Lemma Lagrange : forall n:nat, {a:nat & {b:nat & {c:nat & {d:nat | n=a*a+b*b+c*c+d*d}}}}.
Proof.
intros.
destruct (lagrange_4_square_theorem (Z.of_nat n)) as [a [b [c [d Habcd]]]].
apply Nat2Z.is_nonneg.
exists (Z.abs_nat a).
exists (Z.abs_nat b).
exists (Z.abs_nat c).
exists (Z.abs_nat d).
apply Nat2Z.inj.
repeat rewrite Nat2Z.inj_add.
repeat rewrite Nat2Z.inj_mul.
repeat rewrite Nat2Z.inj_abs_nat.
repeat rewrite Z.abs_square.
apply Habcd.
Qed.

Lemma split_sum n (f : nat -> nat) :
  \sum_(0 <= i < 4 * n + 4) f i =
  \sum_(0 <= i < 4 * n) f i + \sum_(4 * n <= i < 4 * n + 4) f i.
Proof.
by rewrite (big_cat_nat   (leq0n _) (leq_addr 4 (4*n))).
Qed.

Lemma step_sum n (f:nat->nat): \sum_(0 <= i < n.+1) (f i) = \sum_(0 <= i < n) (f i) + f(n).
Proof.
 by rewrite big_nat_recr.
Qed.

Lemma split_4 n f : \sum_(0<=i<4*n) f i = \sum_(0<=i<n) (f (4*i) + f ((4*i).+1) + f ((4*i).+2) + f((4*i).+3)).
Proof.
elim: n => [|n IH].
  by rewrite !big_geq.
replace (4 * n.+1) with (4 * n + 4) by lia.
rewrite split_sum.
rewrite step_sum.
rewrite IH.
apply f_equal.
  have -> :  4 * n + 4 = ((4 * n + 3).+1) by lia. 
  have -> : 4 * n + 3 = (4 * n + 2).+1 by lia.
  have -> : 4 * n + 2 = (4 * n + 1).+1 by lia.
  have -> : 4 * n + 1 = (4 * n).+1 by lia.
rewrite big_nat_recr /=.
rewrite big_nat_recr /=.
rewrite big_nat_recr /=.
rewrite big_nat1 /=.
ring.
lia.
lia.
lia.
Qed.


(*Lemma split_4 n f : Nat.modulo (n+1) mod 4 = 0 -> *)


Open Scope Z_scope.
(*
Definition row4 x0 x1 x2 x3 : 'rV[Z]_4 :=
  \row_(i < 4)
    match i with 0 => x0 | 1 => x1 | 2 => x2 | _ => x3 end.
*)

Definition s (x:Z) := x*x.

Section s3_1_3.
(* Lemma 3.1.3 (Euler’s four square identity). *)

Lemma four_square_identify : forall a1 a2 a3 a4 b1 b2 b3 b4 : Z, 
(s a1 + s a2 + s a3 + s a4) * (s b1 + s b2 + s b3 + s b4) = 
 s (a1*b1 - a2*b2 - a3*b3 - a4*b4)
+ s (a1*b2 + a2*b1 + a3*b4 - a4*b3)
+ s (a1*b3 - a2*b4 + a3*b1 + a4*b2)
+ s (a1*b4 + a2*b3 - a3*b2 + a4*b1).
Proof.
intros; unfold s; ring.
Qed.

End s3_1_3.

Lemma zero_s : forall x:Z, s x=0 -> x = 0.
Proof.
unfold s; intros; nia.
Qed.

Lemma square_zero : forall x y z t:Z, s x + s y + s z + s t =0 <-> x=0/\y=0/\z=0/\t=0.
Proof.
 intros; split.
 unfold s; intros.
 nia.
 intuition subst; reflexivity.
Qed.

Section s3_1_8.

Lemma l3_1_8 : forall a1 a2 b1 b2 :Z,
(s a1 + s a2)*(s b1 + s b2) = s (a1*b1-a2*b2) + s (a1*b2+a2*b1).
Proof.
intros; unfold s; ring.
Qed.

Section s3_1_6.

Variables a1 a2 a3 a4 b1 b2 b3 b4 : Z.
Definition c1 := a1*b1-a2*b2-a3*b3-a4*b4.
Definition c2 := a1*b2+a2*b1+a3*b4-a4*b3.
Definition c3 := a1*b3-a2*b4+a3*b1+a4*b2.
Definition c4 :=a1*b4+a2*b3-a3*b2+a4*b1.

Lemma Habc : (a1*a1 + a2*a2 + a3*a3 + a4*a4)*(b1*b1+b2*b2+b3*b3+b4*b4)=c1*c1+c2*c2+c3*c3+c4*c4.
Proof.
unfold c1,c2,c3,c4; ring.
Qed.

Definition c : 'rV[Z]_4 :=
  \matrix_(i < 1, j < 4)
    match nat_of_ord j with
    | 0%nat => c1
    | 1%nat => c2
    | 2%nat => c3
    | _ => c4
    end.

Definition a : 'rV[Z]_4 :=
  \matrix_(i < 1, j < 4)
    match nat_of_ord j with
    | 0%nat => a1
    | 1%nat => a2
    | 2%nat => a3
    | _ => a4
    end.

Definition B : 'M[Z]_(4,4) :=
  \matrix_(i < 4, j < 4)
     match (nat_of_ord i, nat_of_ord j) with
     | (0%nat,0%nat) => b1 | (0%nat,1%nat) => b2 | (0%nat,2%nat) => b3 | (0%nat,3%nat) => b4
     | (1%nat,0%nat) => -b2 | (1%nat,1%nat) => b1 | (1%nat,2%nat) => -b4 | (1%nat,3%nat) => b3
     | (2%nat,0%nat) => -b3 | (2%nat,1%nat) => b4 | (2%nat,2%nat) => b1 | (2%nat,3%nat) => -b2
     | (3%nat,0%nat) => -b4 | (3%nat,1%nat) => -b3 | (3%nat,2%nat) => b2 | (_,_) => b1
     end.
(*
Locate "*m".
Print mulmx.
Check B.

(*Check (V *m B).*)
Locate "*m".
Check a.
Check B.
(*Check (mulmx a B).*)

Parameter x : 'rV[Z]_4.
Parameter C : 'M[Z]_4.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import algebra.matrix.
About matrix.
Definition y := (x *m C)%R.
*)

Definition n := b1^2 + b2^2 + b3^2 + b4^2.
(*
Lemma BtB_scalar :
  (B^T *m B = n%:M)%R.
Proof.
unfold B.
apply/matrixP => i j.
rewrite mxE.
- case: (i, j) => [i0 j0].
  rewrite !mxE /=.
  repeat case: i0; repeat case: j0; ring.
intros.
cbv.
*)
Lemma aux : (\det B = s (s b1+ s b2 + s b3 + s b4))%R.
Proof.
Admitted.

Lemma foo : forall x y z t, x + y + z +t = (x + (y + (z + t)))%R.
Proof.
by move=> x y z t; rewrite !addrA. 
Qed.

Lemma bar : forall x:Z, (x+0=x)%R.
Proof.
by move=> x; rewrite addr0.
Qed.

Lemma x : (*forall a1 a2 a3 a4) b1 b2 b3 b4 c1 c2 c3 c4:Z, 
  (s a1 + s a2 + s a3 + s a4)*(s b1 + s b2 + s b3 +  s b4) = s c1 + s c2 + s c3 + s c4 -> *)
(c%R = a *m B)%R /\ ((\det  B =0)%R <-> (b1=0/\b2=0/\b3=0/\b4=0)%R).
Proof.
 intros.
 split.

apply/matrixP => i j.
  rewrite !mxE.
unfold c1, c2, c3, c4.
  rewrite !big_ord_recl big_ord0 /=.
  rewrite !mxE /=.
  (* now i : 'I_1 and j : 'I_4, case split on them *)
  case: i => [[|] //] hi.
  case: j => [[|[|[|[|]]]] //] hj /=.

  - (* j = 0 *) 
  replace (a1 * b1 - a2 * b2 - a3 * b3 - a4 * b4) 
  with (a1 * b1 + a2*(-b2) + a3*(-b3) + a4*(-b4)) by ring.
  rewrite bar; apply foo.
  - (* j = 1 *) 
  replace (a1 * b2 + a2 * b1 + a3 * b4 - a4 * b3) 
  with (a1 * b2 + a2*b1 + a3*b4 + a4*(-b3)) by ring.
  rewrite bar; apply foo.
  - (* j = 2 *) 
  replace (a1 * b3 - a2 * b4 + a3 * b1 + a4 * b2) with 
  (a1 * b3 + a2*(-b4) + a3*b1 + a4*b2) by ring.
  rewrite bar; apply foo.
  - (* j = 3 *) 
  replace (a1 * b4 + a2 * b3 - a3 * b2 + a4 * b1) 
  with (a1 * b4 + a2*b3 + a3*(-b2) + a4*b1) by ring.
  rewrite bar; apply foo.

rewrite aux.
split.
intros.
assert (s b1 + s b2 + s b3 + s b4 = 0).
apply zero_s; assumption.
apply square_zero; assumption.

intuition subst; simpl; reflexivity.
Qed.


End s3_1_6.
