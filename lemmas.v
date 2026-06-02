From Coqtail Require Import Arith.Lagrange_four_square.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect perm fingroup all_algebra.

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

Open Scope Z_scope.
(*
Definition row4 x0 x1 x2 x3 : 'rV[Z]_4 :=
  \row_(i < 4)
    match i with 0 => x0 | 1 => x1 | 2 => x2 | _ => x3 end.
*)
Section s3_1_6.

Variables a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 : Z.
Hypothesis Habc : (a1*a1 + a2*a2 + a3*a3 + a4*a4)*(b1*b1+b2*b2+b3*b3+b4*b4)=c1*c1+c2*c2+c3*c3+c4*c4.

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

Locate "*m".
Print mulmx.
(*
Lemma x : forall a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4:Z, 
  (a1*a1 + a2*a2 + a3*a3 + a4*a4)*(b1*b1+b2*b2+b3*b3+b4*b4)=c1*c1+c2*c2+c3*c3+c4*c4 -> 
(c = a *m B)%R /\ (det(B)=0 <-> (b1=b2/\b2=b3/\b3=b4/\b4=0)).
Proof.
Admitted.
*)
End s3_1_6.
