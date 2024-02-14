Require Import PG2X.projective_plane_axioms.

Inductive Point : Set := | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11 | P12.

Inductive Line : Set := | L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | L12.

Definition incid x l := match l with
 | L0 => match x with | P0 | P1 | P2 | P3  => true | _ => false end 
 | L1 => match x with | P0 | P4 | P5 | P6  => true | _ => false end 
 | L2 => match x with | P0 | P8 | P9 | P12  => true | _ => false end 
 | L3 => match x with | P0 | P7 | P10 | P11  => true | _ => false end 
 | L4 => match x with | P1 | P4 | P7 | P8  => true | _ => false end 
 | L5 => match x with | P1 | P6 | P9 | P11  => true | _ => false end 
 | L6 => match x with | P1 | P5 | P10 | P12  => true | _ => false end 
 | L7 => match x with | P3 | P4 | P9 | P10  => true | _ => false end 
 | L8 => match x with | P2 | P4 | P11 | P12  => true | _ => false end 
 | L9 => match x with | P2 | P5 | P7 | P9  => true | _ => false end 
 | L10 => match x with | P3 | P6 | P7 | P12  => true | _ => false end 
 | L11 => match x with | P3 | P5 | P8 | P11  => true | _ => false end 
 | L12 => match x with | P2 | P6 | P8 | P10  => true | _ => false end 
end.

Definition Incid x l := incid x l = true.

Definition l_from_points (x y:Point) := match x with
 | P0 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L1 | P5 => L1 | P6 => L1 | P7 => L3 | P8 => L2 | P9 => L2 | P10 => L3 | P11 => L3 | P12 => L2 end 
 | P1 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L4 | P5 => L6 | P6 => L5 | P7 => L4 | P8 => L4 | P9 => L5 | P10 => L6 | P11 => L5 | P12 => L6 end 
 | P2 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L8 | P5 => L9 | P6 => L12 | P7 => L9 | P8 => L12 | P9 => L9 | P10 => L12 | P11 => L8 | P12 => L8 end 
 | P3 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L7 | P5 => L11 | P6 => L10 | P7 => L10 | P8 => L11 | P9 => L7 | P10 => L7 | P11 => L11 | P12 => L10 end 
 | P4 => match y with | P0 => L1 | P1 => L4 | P2 => L8 | P3 => L7 | P4 => L1 | P5 => L1 | P6 => L1 | P7 => L4 | P8 => L4 | P9 => L7 | P10 => L7 | P11 => L8 | P12 => L8 end 
 | P5 => match y with | P0 => L1 | P1 => L6 | P2 => L9 | P3 => L11 | P4 => L1 | P5 => L1 | P6 => L1 | P7 => L9 | P8 => L11 | P9 => L9 | P10 => L6 | P11 => L11 | P12 => L6 end 
 | P6 => match y with | P0 => L1 | P1 => L5 | P2 => L12 | P3 => L10 | P4 => L1 | P5 => L1 | P6 => L1 | P7 => L10 | P8 => L12 | P9 => L5 | P10 => L12 | P11 => L5 | P12 => L10 end 
 | P7 => match y with | P0 => L3 | P1 => L4 | P2 => L9 | P3 => L10 | P4 => L4 | P5 => L9 | P6 => L10 | P7 => L3 | P8 => L4 | P9 => L9 | P10 => L3 | P11 => L3 | P12 => L10 end 
 | P8 => match y with | P0 => L2 | P1 => L4 | P2 => L12 | P3 => L11 | P4 => L4 | P5 => L11 | P6 => L12 | P7 => L4 | P8 => L2 | P9 => L2 | P10 => L12 | P11 => L11 | P12 => L2 end 
 | P9 => match y with | P0 => L2 | P1 => L5 | P2 => L9 | P3 => L7 | P4 => L7 | P5 => L9 | P6 => L5 | P7 => L9 | P8 => L2 | P9 => L2 | P10 => L7 | P11 => L5 | P12 => L2 end 
 | P10 => match y with | P0 => L3 | P1 => L6 | P2 => L12 | P3 => L7 | P4 => L7 | P5 => L6 | P6 => L12 | P7 => L3 | P8 => L12 | P9 => L7 | P10 => L3 | P11 => L3 | P12 => L6 end 
 | P11 => match y with | P0 => L3 | P1 => L5 | P2 => L8 | P3 => L11 | P4 => L8 | P5 => L11 | P6 => L5 | P7 => L3 | P8 => L11 | P9 => L5 | P10 => L3 | P11 => L3 | P12 => L8 end 
 | P12 => match y with | P0 => L2 | P1 => L6 | P2 => L8 | P3 => L10 | P4 => L8 | P5 => L6 | P6 => L10 | P7 => L10 | P8 => L2 | P9 => L2 | P10 => L6 | P11 => L8 | P12 => L2 end 
end.

Lemma a1_exist : forall (A B : Point) , {l : Line | Incid A l /\ Incid B l}.
Proof. intros A B; exists (l_from_points A B); destruct A; destruct B; exact_no_check (conj (@eq_refl bool true)(@eq_refl bool true)). Qed.

Definition p_from_lines (x y:Line) := match x with
 | L0 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P1 | L5 => P1 | L6 => P1 | L7 => P3 | L8 => P2 | L9 => P2 | L10 => P3 | L11 => P3 | L12 => P2 end 
 | L1 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P4 | L5 => P6 | L6 => P5 | L7 => P4 | L8 => P4 | L9 => P5 | L10 => P6 | L11 => P5 | L12 => P6 end 
 | L2 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P8 | L5 => P9 | L6 => P12 | L7 => P9 | L8 => P12 | L9 => P9 | L10 => P12 | L11 => P8 | L12 => P8 end 
 | L3 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P7 | L5 => P11 | L6 => P10 | L7 => P10 | L8 => P11 | L9 => P7 | L10 => P7 | L11 => P11 | L12 => P10 end 
 | L4 => match y with | L0 => P1 | L1 => P4 | L2 => P8 | L3 => P7 | L4 => P1 | L5 => P1 | L6 => P1 | L7 => P4 | L8 => P4 | L9 => P7 | L10 => P7 | L11 => P8 | L12 => P8 end 
 | L5 => match y with | L0 => P1 | L1 => P6 | L2 => P9 | L3 => P11 | L4 => P1 | L5 => P1 | L6 => P1 | L7 => P9 | L8 => P11 | L9 => P9 | L10 => P6 | L11 => P11 | L12 => P6 end 
 | L6 => match y with | L0 => P1 | L1 => P5 | L2 => P12 | L3 => P10 | L4 => P1 | L5 => P1 | L6 => P1 | L7 => P10 | L8 => P12 | L9 => P5 | L10 => P12 | L11 => P5 | L12 => P10 end 
 | L7 => match y with | L0 => P3 | L1 => P4 | L2 => P9 | L3 => P10 | L4 => P4 | L5 => P9 | L6 => P10 | L7 => P3 | L8 => P4 | L9 => P9 | L10 => P3 | L11 => P3 | L12 => P10 end 
 | L8 => match y with | L0 => P2 | L1 => P4 | L2 => P12 | L3 => P11 | L4 => P4 | L5 => P11 | L6 => P12 | L7 => P4 | L8 => P2 | L9 => P2 | L10 => P12 | L11 => P11 | L12 => P2 end 
 | L9 => match y with | L0 => P2 | L1 => P5 | L2 => P9 | L3 => P7 | L4 => P7 | L5 => P9 | L6 => P5 | L7 => P9 | L8 => P2 | L9 => P2 | L10 => P7 | L11 => P5 | L12 => P2 end 
 | L10 => match y with | L0 => P3 | L1 => P6 | L2 => P12 | L3 => P7 | L4 => P7 | L5 => P6 | L6 => P12 | L7 => P3 | L8 => P12 | L9 => P7 | L10 => P3 | L11 => P3 | L12 => P6 end 
 | L11 => match y with | L0 => P3 | L1 => P5 | L2 => P8 | L3 => P11 | L4 => P8 | L5 => P11 | L6 => P5 | L7 => P3 | L8 => P11 | L9 => P5 | L10 => P3 | L11 => P3 | L12 => P8 end 
 | L12 => match y with | L0 => P2 | L1 => P6 | L2 => P8 | L3 => P10 | L4 => P8 | L5 => P6 | L6 => P10 | L7 => P10 | L8 => P2 | L9 => P2 | L10 => P6 | L11 => P8 | L12 => P2 end 
end.

Lemma a2_exist : forall (l1 l2 : Line), {A : Point | Incid A l1 /\ Incid A l2}.
Proof. intros l1 l2; exists (p_from_lines l1 l2); destruct l1; destruct l2; exact_no_check (conj (@eq_refl bool true)(@eq_refl bool true)). Qed.

Lemma foo : forall P:Prop, false=true -> P.
Proof. intros P H; discriminate. Qed.

Lemma points_line : forall T Z:Point, forall x:Line,
      Incid T x -> Incid Z x -> ~T=Z -> x = (l_from_points T Z).
Proof.
  intros T Z x; case x; case T; intros HTx; 
       solve [ exact (foo _ HTx) | 
                case Z; intros HZx HTZ;
                solve  [ exact (foo _ HZx) |  exact (@eq_refl Line _) | exact (False_rect _ (HTZ eq_refl)) ] ].
Qed.

Ltac handle x := match goal with Ht  : (Incid ?T x), Hz  : (Incid ?Z x), Htz : ~ (?T = ?Z)  |- _ =>
                  let HP := fresh in pose proof (points_line T Z x Ht Hz Htz) as HP; clear Ht Hz; rewrite HP end.

Lemma eq_Point_dec : forall A B:Point, {A=B}+{~A=B}.
Proof. intros; destruct A; destruct B; solve [left; reflexivity | right; intro; discriminate]. Qed.

Lemma uniqueness : forall (A B : Point)(l1 l2 : Line),
  Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A = B \/ l1 = l2.
Proof. intros; destruct (eq_Point_dec A B) ; [left; assumption | right; intros; handle l1; handle l2; reflexivity]. Qed.

Definition f_a3_1 (l:Line) := match l with | L0 => (P0,(P1,P2)) | L1 => (P0,(P4,P5)) | L2 => (P0,(P8,P9)) | L3 => (P0,(P7,P10)) | L4 => (P1,(P4,P7)) | L5 => (P1,(P6,P9)) | L6 => (P1,(P5,P10)) | L7 => (P3,(P4,P9)) | L8 => (P2,(P4,P11)) | L9 => (P2,(P5,P7)) | L10 => (P3,(P6,P7)) | L11 => (P3,(P5,P8)) | L12 => (P2,(P6,P8))end.

Lemma a3_1 : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A = B /\ ~ A = C /\ ~ B = C /\ Incid A l /\ Incid B l /\ Incid C l)}}}.
Proof.
 intros l; pose (xyz := f_a3_1 l); exists (fst xyz); exists (fst (snd xyz)); exists (snd (snd xyz)).
  destruct l; solve [split; [intro; discriminate | split; [intro; discriminate | split; [intro; discriminate | split; [reflexivity | split; reflexivity]]]]].
 Qed.

Lemma a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.
Proof. exists L1; exists L2; intro;discriminate. Qed.

Module pg23 : ProjectivePlane.

  Definition Point := Point.
  Definition Line := Line.

  Definition Incid := Incid.

  Lemma a1_exist : forall (A B : Point) , {l : Line | Incid A l /\ Incid B l}.
  Proof. exact a1_exist. Qed.

  Lemma a2_exist : forall (l1 l2 : Line), {A : Point | Incid A l1 /\ Incid A l2}.
  Proof. exact a2_exist. Qed.

  Lemma uniqueness : forall (A B : Point)(l1 l2 : Line),
      Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A = B \/ l1 = l2.
  Proof. exact uniqueness. Qed.

  Lemma a3_1 : forall l : Line,
      {A : Point & {B : Point & {C : Point |
           (~ A = B /\ ~ A = C /\ ~ B = C /\ Incid A l /\ Incid B l /\ Incid C l)}}}.
  Proof. exact a3_1. Qed.

  Lemma a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.
  Proof. exact a3_2. Qed.

End pg23.

