From HB Require Import structures.
From mathcomp Require Import all_ssreflect fingroup.

Class ProjectivePlane (point : finType) (line : finType) (incid : point -> line -> bool) :=
{

a1_exist : forall (A B : point) , {l : line | incid A l /\ incid B l};

a2_exist : forall (l1 l2 : line), {A : point | incid A l1 /\ incid A l2};

uniqueness : forall (A B : point)(l1 l2 : line),
  incid A l1 -> incid B l1  -> incid A l2 -> incid B l2 -> A == B \/ l1 == l2;

(*Definition quadrangle A B C D := forall l : line, A <> B /\ A <>C /\ A <> D /\ B <> C /\ B <> D /\ C <> D
  /\ (incid A l /\ incid B l -> ~incid) C l /\ ~incid D l)
  /\ (incid A l /\ incid C l -> ~incid B l /\ ~incid D l)
  /\ (incid A l /\ incid D l -> ~incid C l /\ ~incid B l)
  /\ (incid C l /\ incid B l -> ~incid A l /\ ~incid D l)
  /\ (incid D l /\ incid B l -> ~incid C l /\ ~incid A l)
  /\ (incid C l /\ incid D l -> ~incid B l /\ ~incid A l).*)

 a3 (* quadrangle *) : {A : point & {B : point & {C : point & {D : point |
  forall l : line, A != B /\ A !=C /\ A != D /\ B != C /\ B !=D /\ C!= D
  /\ (incid A l /\ incid B l -> ~incid C l /\ ~incid D l)
  /\ (incid A l /\ incid C l -> ~incid B l /\ ~incid D l)
  /\ (incid A l /\ incid D l -> ~incid C l /\ ~incid B l)
  /\ (incid C l /\ incid B l -> ~incid A l /\ ~incid D l)
  /\ (incid D l /\ incid B l -> ~incid C l /\ ~incid A l)
  /\ (incid C l /\ incid D l -> ~incid B l /\ ~incid A l)}}}};

(* a3_1 : forall l : line, {A : point & {B : point & {C : point |
  (~ A = B /\ ~ A = C /\ ~ B = C /\ incid A l /\ incid B l /\ incid C l)}}}.*)
(* a3_2 : {l1 : line & {l2 : line | l1 <> l2}}.*)
}.

Section min.

Context
  {point : finType}
  {line : finType}
  {incid : point -> line -> bool}
  {PP : ProjectivePlane point line incid}.

Lemma a1_unique:forall (A B :point)(l1 l2:line),
      A!=B -> incid A l1 -> incid B l1  -> incid A l2 -> incid B l2 -> l1==l2.
Proof.
intros.
generalize (uniqueness A B l1 l2 H0 H1 H2 H3); intros [H' | H'].
rewrite H' in H.
discriminate.
assumption.
Qed.

Lemma a2_unique : forall(l1 l2 :line)(A B :point), 
  l1!=l2 -> incid A l1 -> incid A l2 -> incid B l1 -> incid B l2 -> A==B.
Proof.
intros.
generalize (uniqueness A B l1 l2 H0 H2 H1 H3); intros [H' | H'].
assumption.
rewrite H' in H.
discriminate.
Qed.

Definition join (x y: point) := sval (a1_exist x y).
Definition meet(l1 l2: line) := sval (a2_exist l1 l2).

Lemma incid_x_xy : forall x y : point, incid x (join x y).
Proof.
  unfold join; intros; destruct (a1_exist x y); simpl; tauto.
Qed.

Lemma incid_y_xy : forall x y : point, incid y (join x y).
Proof.
  unfold join; intros; destruct (a1_exist x y); simpl; tauto.
Qed.

Lemma incid_A_l1l2_l1 : forall A:point, forall l1 l2:line, A = meet l1  l2 -> incid A l1.
Proof.
  unfold meet; intros; revert H. 
  destruct (a2_exist l1 l2); simpl.
  intros; subst; tauto.
Qed. 

Lemma incid_A_l1l2_l2 : forall A:point, forall l1 l2:line, A = meet l1  l2 -> incid A l2.
Proof.
  unfold meet; intros; revert H. 
  destruct (a2_exist l1 l2); simpl.
  intros; subst; tauto.
Qed. 

Lemma incid_dec : forall (A : point)(l : line), {incid A l} + {~incid A l}.
Proof.
 intros A l; destruct (incid A l).
left; trivial.
right; discriminate.
Qed.

(* at least 3 points per line from the axioms *)
Definition dist3 (A B C:point) := 
  A <> B /\ A <>C /\ B <> C.

Definition dist4 (A B C D:point) := 
  A <> B /\ A <>C /\ A <> D /\ B <> C /\ B <> D /\ C <> D.

Lemma incidABl : forall (A B:point)(l:line), ~incid A l /\ incid B l -> A <> B.
Proof.
intros l1 l2 A H Hl2l1; subst l1; tauto.
Qed.

Lemma cas1:forall (A B C D : point)(l:line),
  dist4 A B C D /\ incid A l /\incid B l /\ ~incid C l /\ ~incid D l  -> 
  (forall m : line,
       dist4 A B C D /\
       (incid A m /\ incid B m -> ~ incid C m /\ ~ incid D m) /\
       (incid A m /\ incid C m -> ~ incid B m /\ ~ incid D m) /\
       (incid A m /\ incid D m -> ~ incid C m /\ ~ incid B m) /\
       (incid C m /\ incid B m -> ~ incid A m /\ ~ incid D m) /\
       (incid D m /\ incid B m -> ~ incid C m /\ ~ incid A m) /\
       (incid C m /\ incid D m -> ~ incid B m /\ ~ incid A m)) -> 
  {E:point | dist3 A B E/\incid E l}.
Proof.
intros A B C D l H Hincid.
elim (a1_exist C D).
intros l1 Hl1.
assert(C <> D) by (unfold dist4 in H; tauto).

elim (a2_exist l l1).
intros E HE.
exists E.
split.

unfold dist3.
split.
unfold dist4 in H; tauto.

split.
intros HAE.
subst E.
generalize (Hincid l1); intros H'.
tauto.

intros HBE.
subst E.
generalize (Hincid l1); intros H'.
tauto.

tauto.

Qed.
(* Cas 2 : 1 point sur L, 3 points n'y sont pas. Il faut construire 2 points de L 
   par intersection avec des lignes engendrees par les points n'appartenant pas a  L. 
   Il faut faire des cas sur les points choisis et les risques d'alignement. 
*)


Lemma cas2:forall (A B C D : point)(l:line),
  dist4 A B C D /\ incid A l /\ ~incid B l /\ ~incid C l /\ ~incid D l ->
  (forall m : line,
       dist4 A B C D /\
       (incid A m /\ incid B m -> ~ incid C m /\ ~ incid D m) /\
       (incid A m /\ incid C m -> ~ incid B m /\ ~ incid D m) /\
       (incid A m /\ incid D m -> ~ incid C m /\ ~ incid B m) /\
       (incid C m /\ incid B m -> ~ incid A m /\ ~ incid D m) /\
       (incid D m /\ incid B m -> ~ incid C m /\ ~ incid A m) /\
       (incid C m /\ incid D m -> ~ incid B m /\ ~ incid A m)) ->
  {E:point &{F:point |
    dist3 A E F/\incid E l /\ incid F l}}.
Proof.
intros A B C D l H Hincid.
elim (a1_exist B C).
intros d1 Hd1.
assert (B<>C).
unfold dist4 in H; tauto.
elim (a2_exist l d1).
intros IBC HIBC.
elim (incid_dec A d1).
intros HAd1.

elim (Hincid d1).
tauto.
intros HAd1.

elim (a1_exist B D).
intros d2 Hd2.
assert (B<>D) by (unfold dist4 in H; tauto).
elim (a2_exist l d2).
intros IBD HIBD.
elim (incid_dec A d2).
intros HAd2.
elim (Hincid d2).
tauto.
intros HAd2.
exists IBC. 
exists IBD.
split.
unfold dist3.
split.
intros HAIBC.
subst.
apply HAd1.
tauto.
split.
intros HAIBD.
subst.
apply HAd1.
tauto.
assert (d1 <> d2).
intros Hd1d2.
subst.
elim (Hincid d2); tauto.

elim Hd1; intros Hd1B Hd1C.
elim Hd2; intros Hd2B Hd2D.
elim HIBC; intros HIBCl HIBCd1.
elim (incid_dec IBC d2).
intros HIBCd2.
assert (H2':d1!=d2) by (by apply/eqP).

generalize (a2_unique d1 d2 B IBC H2' Hd1B Hd2B HIBCd1 HIBCd2).
intros HBIBC.
assert (B=IBC) by (by apply/eqP). 
subst.
assert (IBD<>IBC).
intuition.
eapply incidABl with (l:=l). 
tauto.
intros HIBDd2.

intros H'.
subst.
apply HIBDd2.
tauto.
split.
tauto.
tauto.
Qed.

(* Cas 3 : 0 point sur L, 4 points n'y sont pas. On doit mener le meme raisonnement 
   que pour le cas 2, mais avec un plus grand nombre de sous-cas. 
*)


Lemma cas3:forall (A B C D : point)(l:line),
  dist4 A B C D /\ ~incid A l /\~incid B l /\ ~incid C l /\ ~incid D l ->
  (forall m : line,
    dist4  A B C D /\
    (incid A m /\ incid B m -> ~ incid C m /\ ~ incid D m) /\
    (incid A m /\ incid C m -> ~ incid B m /\ ~ incid D m) /\
    (incid A m /\ incid D m -> ~ incid C m /\ ~ incid B m) /\
    (incid C m /\ incid B m -> ~ incid A m /\ ~ incid D m) /\
    (incid D m /\ incid B m -> ~ incid C m /\ ~ incid A m) /\
    (incid C m /\ incid D m -> ~ incid B m /\ ~ incid A m)) ->
  {E:point & {F:point & {G:point |
    dist3 E F G/\incid E l/\incid F l/\incid G l}}}.
Proof.
intros A B C D l H Hincid.
elim(a1_exist A B).
intros l1 Hl1.

elim(a1_exist A C).
intros l2 Hl2.

elim(a1_exist A D).
intros l3 Hl3.

elim (a2_exist l l1).
intros I HI.
elim (a2_exist l l2).
intros J HJ.
elim (a2_exist l l3).
intros K HK.

elim HI; intros HIl HIl1.
elim HJ; intros HJl HJl2.
(* 1 *)
elim (incid_dec I l2).
intros HIl2.
assert (Hl1l2 : l<>l2).
intros Hl1l2.
subst.
elim (Hincid l2); tauto.
assert (Hl1l2':l!=l2) by (by apply/eqP).
generalize (a2_unique l l2 I J Hl1l2' HIl HIl2 HJl HJl2).
move => /eqP HIJ.

subst.
assert (A<>J).
eapply incidABl with (l:=l).
tauto.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
assert (H0': A !=J) by (by apply/eqP).
generalize (a1_unique A J l1 l2 H0' HAl1 HIl1 HAl2 HIl2).
move => /eqP H'; subst.
elim (Hincid l2); tauto.
(* 1 *)
intros HIl2.
elim (incid_dec I l3).
intros HIl3.
assert (Hl1l3 : l<>l3).
intros Hl1l3.
subst.
elim (Hincid l3); tauto.
elim HK; intros HKl HKl3.
assert (Hl1l3' : l!=l3) by (by apply/eqP).
generalize (a2_unique l l3 I K Hl1l3' HIl HIl3 HKl HKl3).
move => /eqP HIK.
subst.
assert (A<>K).
eapply incidABl with (l:=l).
tauto.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
elim Hl3; intros HAl3 HDl3.
assert (H0': A!=K) by (by apply/eqP).
generalize (a1_unique A K l1 l3 H0' HAl1 HIl1 HAl3 HIl3).
move => /eqP H'; subst.
elim (Hincid l3); tauto.
intros HIl3.

elim (incid_dec J l1).
intros HJl1.
assert (Hll1 : l<>l1).
intros Hll1.
subst.
elim (Hincid l1); tauto.
assert (Hll1':l!=l1) by (by apply/eqP).
generalize (a2_unique l l1 I J Hll1' HIl HIl1 HJl HJl1).
move => /eqP HIJ.
subst.
assert (Hf:False).
apply HIl2.
assumption.
elim Hf.
intros HJl1.
elim (incid_dec K l2).
intros HKl2.
assert (Hll2 : l<>l2).
intros Hll2.
subst.
elim (Hincid l3); tauto.
elim HK; intros HKl HKl3.
assert (Hll2': l != l2) by (by apply/eqP).
generalize (a2_unique l l2 J K Hll2' HJl HJl2 HKl HKl2).
move => /eqP HJK.
subst.
assert (A<>K).
eapply incidABl with (l:=l).
tauto.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
elim Hl3; intros HAl3 HDl3.
assert (H0':A != K) by (by apply/eqP).
generalize (a1_unique A K l2 l3 H0' HAl2 HJl2 HAl3 HKl3).
move => /eqP H'; subst.
elim (Hincid l3); tauto.
intros HKl2.
exists I.
exists J.
exists K.
split.
unfold dist3.
split.
eapply incidABl with (l:=l2).
tauto.
split.
eapply incidABl with (l:=l3).
tauto.
assert (K<>J).
eapply incidABl with (l:=l2).
tauto.
auto.
tauto.
Qed.

Lemma a3_1 : 
  (forall l:line,{A:point & {B:point & {C:point | (dist3 A B C/\incid A l /\incid B l /\ incid C l)}}}).
generalize a3.
intros _H.
assert (H:{A : point &
  {B : point &
  {C : point &
  {D : point
  | forall l : line,
    dist4 A B C D /\
    (incid A l /\ incid B l -> ~ incid C l /\ ~ incid D l) /\
    (incid A l /\ incid C l -> ~ incid B l /\ ~ incid D l) /\
    (incid A l /\ incid D l -> ~ incid C l /\ ~ incid B l) /\
    (incid C l /\ incid B l -> ~ incid A l /\ ~ incid D l) /\
    (incid D l /\ incid B l -> ~ incid C l /\ ~ incid A l) /\
    (incid C l /\ incid D l -> ~ incid B l /\ ~ incid A l)}}}}).
destruct _H as [ A [ B [ C [ D HABCD]]]].
exists A; exists B; exists C; exists D.
intros l.
decompose [and] (HABCD l).
split; [idtac | tauto].
unfold dist4; repeat split; move => /eqP Hdiff. 
by rewrite Hdiff in H.
by rewrite Hdiff in H1.
by rewrite Hdiff in H0.
by rewrite Hdiff in H2.
by rewrite Hdiff in H3.
by rewrite Hdiff in H4.

intros l.
elim H; clear H; intros A HA.
elim HA; clear HA; intros B HB.
elim HB; clear HB; intros C HC.
elim HC; clear HC; intros D HD.
elim (HD l).
intros Hdist Hincid.
elim (incid_dec A l).
intros HAl.
elim (incid_dec B l).
intros HBl.
elim (incid_dec C l).
intros HCl.
assert False by tauto.
tauto.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert False by tauto.
tauto.
intros HDl.
assert ( H' : dist4 A B C D /\ incid A l /\ incid B l /\ ~ incid C l /\ ~ incid D l).
tauto.

elim (cas1 A B C D l H' HD).
intros E HE.
exists A.
exists B.
exists E.
tauto.

intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert ( H' : dist4 A B C D /\ incid A l /\ ~ incid B l /\ ~ incid C l /\ ~ incid D l).
tauto.
elim (cas2 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
exists A.
exists E.
exists F.
tauto.
intros HDl.
assert (H' : dist4 A C B D /\ incid A l /\ incid C l /\ ~ incid B l /\ ~ incid D l).
unfold dist4 in * ;intuition.
assert (HD' : forall m : line,
  dist4 A C B D /\
  (incid A m /\ incid C m -> ~ incid B m /\ ~ incid D m) /\
  (incid A m /\ incid B m -> ~ incid C m /\ ~ incid D m) /\
  (incid A m /\ incid D m -> ~ incid B m /\ ~ incid C m) /\
  (incid B m /\ incid C m -> ~ incid A m /\ ~ incid D m) /\
  (incid D m /\ incid C m -> ~ incid B m /\ ~ incid A m) /\
  (incid B m /\ incid D m -> ~ incid C m /\ ~ incid A m)).
intros m; elim (HD m); clear HD.
intuition.
generalize (cas1 A C B D l H' HD').
intros H'' ; elim H''; intros E HE.
exists A.
exists C.
exists E.
tauto.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' :(dist4 A D B C /\ incid A l /\ incid D l /\ ~ incid B l /\ ~ incid C l)).
unfold dist4 in *; intuition.
assert (HD' : (forall m : line,
     dist4 A D B C /\
     (incid A m /\ incid D m -> ~ incid B m /\ ~ incid C m) /\
     (incid A m /\ incid B m -> ~ incid D m /\ ~ incid C m) /\
     (incid A m /\ incid C m -> ~ incid B m /\ ~ incid D m) /\
     (incid B m /\ incid D m -> ~ incid A m /\ ~ incid C m) /\
     (incid C m /\ incid D m -> ~ incid B m /\ ~ incid A m) /\
     (incid B m /\ incid C m -> ~ incid D m /\ ~ incid A m))).
intros m; elim (HD m); clear HD.
unfold dist4; solve [intuition].
elim (cas1 A D B C l H' HD').
intros E HE.
exists A.
exists D.
exists E.
tauto.
intros HDl.
assert ( H' : dist4 A B C D /\ incid A l /\ ~ incid B l /\ ~ incid C l /\ ~ incid D l).
intuition.
elim (cas2 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
exists A.
exists E.
exists F.
tauto.
intros HAl.
elim (incid_dec B l).
intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert False by tauto.
tauto.
intros HDl.
assert (H' : dist4 B C A D /\ incid B l /\ incid C l /\ ~ incid A l /\ ~ incid D l).
unfold dist4 in *; intuition.
assert (HD' : (forall m :line,
     dist4  B C A D /\
     (incid B m /\ incid C m -> ~ incid A m /\ ~ incid D m) /\
     (incid B m /\ incid A m -> ~ incid C m /\ ~ incid D m) /\
     (incid B m /\ incid D m -> ~ incid A m /\ ~ incid C m) /\
     (incid A m /\ incid C m -> ~ incid B m /\ ~ incid D m) /\
     (incid D m /\ incid C m -> ~ incid A m /\ ~ incid B m) /\
     (incid A m /\ incid D m -> ~ incid C m /\ ~ incid B m))).
intros m; elim (HD m); clear HD.
unfold dist4; solve [intuition].
elim (cas1 B C A D l H' HD').
intros E HE.
exists B.
exists C.
exists E.
tauto.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : dist4 B D A C /\ incid B l /\ incid D l /\ ~ incid A l /\ ~ incid C l).
unfold dist4 in *; intuition.
assert (HD' : (forall m : line,
     dist4 B D A C /\
     (incid B m /\ incid D m -> ~ incid A m /\ ~ incid C m) /\
     (incid B m /\ incid A m -> ~ incid D m /\ ~ incid C m) /\
     (incid B m /\ incid C m -> ~ incid A m /\ ~ incid D m) /\
     (incid A m /\ incid D m -> ~ incid B m /\ ~ incid C m) /\
     (incid C m /\ incid D m -> ~ incid A m /\ ~ incid B m) /\
     (incid A m /\ incid C m -> ~ incid D m /\ ~ incid B m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; solve [intuition].
elim (cas1 B D A C l H' HD').
intros E HE.
exists B.
exists D.
exists E.
tauto.
intros HDl.
assert (H' : dist4 B A C D /\ incid B l /\ ~ incid A l /\ ~ incid C l /\ ~ incid D l).
unfold dist4 in *; intuition.
assert (HD'  :  (forall m : line,
     dist4 B A C D /\
     (incid B m /\ incid A m -> ~ incid C m /\ ~ incid D m) /\
     (incid B m /\ incid C m -> ~ incid A m /\ ~ incid D m) /\
     (incid B m /\ incid D m -> ~ incid C m /\ ~ incid A m) /\
     (incid C m /\ incid A m -> ~ incid B m /\ ~ incid D m) /\
     (incid D m /\ incid A m -> ~ incid C m /\ ~ incid B m) /\
     (incid C m /\ incid D m -> ~ incid A m /\ ~ incid B m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; solve [intuition].
elim (cas2 B A C D l H' HD').  
intros E HE.
elim HE; intros F HF.
exists B.
exists E.
exists F.
tauto.
intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : dist4 C D A B /\ incid C l /\ incid D l /\ ~ incid A l /\ ~ incid B l).
unfold dist4 in *; intuition.
assert (HD' : (forall m : line,
     dist4 C D A B /\
     (incid C m /\ incid D m -> ~ incid A m /\ ~ incid B m) /\
     (incid C m /\ incid A m -> ~ incid D m /\ ~ incid B m) /\
     (incid C m /\ incid B m -> ~ incid A m /\ ~ incid D m) /\
     (incid A m /\ incid D m -> ~ incid C m /\ ~ incid B m) /\
     (incid B m /\ incid D m -> ~ incid A m /\ ~ incid C m) /\
     (incid A m /\ incid B m -> ~ incid D m /\ ~ incid C m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; solve [intuition].
elim (cas1 C D A B l H' HD').
intros E HE.
exists C.
exists D.
exists E.
tauto.
intros HDl.
assert (H' : (dist4 C A B D /\ incid C l /\ ~ incid A l /\ ~ incid B l /\ ~ incid D l)).
unfold dist4 in *; intuition.
assert (HD' : (forall m : line,
     dist4 C A B D /\
     (incid C m /\ incid A m -> ~ incid B m /\ ~ incid D m) /\
     (incid C m /\ incid B m -> ~ incid A m /\ ~ incid D m) /\
     (incid C m /\ incid D m -> ~ incid B m /\ ~ incid A m) /\
     (incid B m /\ incid A m -> ~ incid C m /\ ~ incid D m) /\
     (incid D m /\ incid A m -> ~ incid B m /\ ~ incid C m) /\
     (incid B m /\ incid D m -> ~ incid A m /\ ~ incid C m))).
intros m; elim (HD m); clear HD.
unfold dist4; solve [intuition].
elim (cas2 C A B D l H' HD').
intros E HE.
elim HE; intros F HF.
exists C.
exists E.
exists F.
tauto.
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : dist4 D A B C /\ incid D l /\ ~ incid A l /\ ~ incid B l /\ ~ incid C l).
unfold dist4 in *; intuition.
assert (HD' : (forall m : line,
     dist4 D A B C /\
     (incid D m /\ incid A m -> ~ incid B m /\ ~ incid C m) /\
     (incid D m /\ incid B m -> ~ incid A m /\ ~ incid C m) /\
     (incid D m /\ incid C m -> ~ incid B m /\ ~ incid A m) /\
     (incid B m /\ incid A m -> ~ incid D m /\ ~ incid C m) /\
     (incid C m /\ incid A m -> ~ incid B m /\ ~ incid D m) /\
     (incid B m /\ incid C m -> ~ incid A m /\ ~ incid D m))).
intros m; elim (HD m); clear HD.
unfold dist4 in *; solve [intuition].
elim (cas2 D A B C l H' HD').
intros E HE.
elim HE; intros F HF.
exists D.
exists E.
exists F.
tauto.
intros HDl.
assert (H' : dist4 A B C D /\ ~ incid A l /\ ~ incid B l /\ ~ incid C l /\ ~ incid D l).
unfold dist4 in *; solve [intuition].
elim (cas3 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
elim HF; intros G HG.
exists E.
exists F.
exists G.
tauto.
Qed.

Lemma a3_2 : {l1 : line & {l2 : line | l1 <> l2}}.
Proof.
destruct a3 as [A [ B [C [D HABCD]]]].
exists (join A B).
exists (join C D).
intro.
assert (incid A (join A B) /\ incid B (join A B)).
split.
apply incid_x_xy.
apply incid_y_xy.
assert (incid C (join A B) /\ incid D (join A B)).
rewrite H.
split.
apply incid_x_xy.
apply incid_y_xy.
assert (~incid C (join A B) /\ ~incid D (join A B)).
destruct (HABCD (join A B)).
decompose [and] H3; auto.
tauto.
Qed.



Lemma a3l (*quadrilateral*) :  {A : line & {B : line & {C : line & {D : line |
  forall l : point, A != B /\ A !=C /\ A != D /\ B != C /\ B !=D /\ C!= D
  /\ (incid l A /\ incid l B -> ~incid l C /\ ~incid l D)
  /\ (incid l A /\ incid l C -> ~incid l B /\ ~incid l D)
  /\ (incid l A /\ incid l D -> ~incid l C /\ ~incid l B)
  /\ (incid l C /\ incid l B -> ~incid l A /\ ~incid l D)
  /\ (incid l D /\ incid l B -> ~incid l C /\ ~incid l A)
  /\ (incid l C /\ incid l D -> ~incid l B /\ ~incid l A)}}}}.
Proof.
  destruct a3 as [A [B [C [D HABCD]]]].
  exists (join A B); exists (join B C); exists (join C D); exists (join D A).
  intros.
  assert (HABCD': 
  A != B /\
  A != C /\
  A != D /\
  B != C /\
  B != D /\
  C != D /\
  forall l : line, (incid A l /\ incid B l -> ~ incid C l /\ ~ incid D l) /\
  (incid A l /\ incid C l -> ~ incid B l /\ ~ incid D l) /\
  (incid A l /\ incid D l -> ~ incid C l /\ ~ incid B l) /\
  (incid C l /\ incid B l -> ~ incid A l /\ ~ incid D l) /\
  (incid D l /\ incid B l -> ~ incid C l /\ ~ incid A l) /\
  (incid C l /\ incid D l -> ~ incid B l /\ ~ incid A l)).
solve [firstorder].
clear HABCD.
destruct HABCD' as [HAB [HAC [HAD [HBC [HBD [HCD Hl]]]]]].
split.

Ltac solveY := apply/eqP; intro; match goal with H: join ?A ?B = join ?C ?D |- _ => 
  assert (incid A (join A B)) by apply incid_x_xy; 
  assert (incid B (join A B)) by apply incid_y_xy;
  assert (incid C (join A B)) by (rewrite H;solve [apply incid_x_xy | apply incid_y_xy]);
  assert (incid D (join A B)) by (rewrite H;solve [apply incid_x_xy | apply incid_y_xy]);
  match goal with Hl :
      forall l : _, _  |- _ => 
      generalize (Hl (join A B)); intro; tauto end end. 
solveY.
split.
solveY.
split.
solveY.
split.
solveY.
split.
solveY.
split.
solveY.




Admitted.

Ltac solveX := 
  apply/eqP; intro;
  match goal with 
    H: (?V = meet (join ?X ?Y) (join ?Z ?T))  |- False => 
  assert (incid V (join X Y)) by (eapply incid_A_l1l2_l1; eauto);
  assert (incid V (join Z T)) by (eapply incid_A_l1l2_l2; eauto);
  assert (incid X (join X Y)) by apply incid_x_xy;
  assert (incid Y (join X Y)) by apply incid_y_xy;
  assert (incid Z (join Z T)) by apply incid_x_xy;
  assert (incid T (join Z T))by apply incid_y_xy;
    match goal with Hl :
      forall l : _, _  |- _ => 
      generalize (Hl (join Z T)); generalize (Hl (join X Y)); intros;tauto end end.

Lemma seven_points : { P:point & {Q & {R & {S & {T & {U & {V | 
  uniq [::P;Q;R;S;T;U;V]}}}}}}}.
Proof.
destruct a3 as [A [B [C [D HABCD]]]].
assert (HABCD': 
  A != B /\
  A != C /\
  A != D /\
  B != C /\
  B != D /\
  C != D /\
  forall l : line, (incid A l /\ incid B l -> ~ incid C l /\ ~ incid D l) /\
  (incid A l /\ incid C l -> ~ incid B l /\ ~ incid D l) /\
  (incid A l /\ incid D l -> ~ incid C l /\ ~ incid B l) /\
  (incid C l /\ incid B l -> ~ incid A l /\ ~ incid D l) /\
  (incid D l /\ incid B l -> ~ incid C l /\ ~ incid A l) /\
  (incid C l /\ incid D l -> ~ incid B l /\ ~ incid A l)).
solve [firstorder].
clear HABCD.
destruct HABCD' as [HAB [HAC [HAD [HBC [HBD [HCD Hl]]]]]].

exists A.
exists B.
exists C.
exists D.
exists (meet (join A B) (join C D)).
exists (meet (join A C) (join B D)).
exists (meet (join A D) (join B C)).

have hA1 : A!=meet (join A B) (join C D). 
solveX.
have hA2 : A!=meet (join A C) (join B D).
solveX.
have hA3 : A!=meet (join A D) (join B C).
solveX.
have hB1 : B!=meet (join A B) (join C D).
solveX.
have hB2 : B!=meet (join A C) (join B D).
solveX.
have hB3 : B!=meet (join A D) (join B C).
solveX.
have hC1 : C!=meet (join A B) (join C D).
solveX.
have hC2 : C!= meet (join A C) (join B D).
solveX.
have hC3 : C!= meet (join A D) (join B C).
solveX.
have hD1 : D!= meet (join A B) (join C D).
solveX.
have hD2 : D!= meet (join A C) (join B D).
solveX.
have hD3 : D!= meet (join A D) (join B C).
solveX.
have hmj1 :  meet (join A B) (join C D) != meet (join A C) (join B D).
apply/eqP; intro.

assert (incid (meet (join A B) (join C D)) (join A B)).
apply (incid_A_l1l2_l1 (meet (join A B) (join C D)) (join A B) (join C D) (erefl _)).
assert (incid (meet (join A B) (join C D)) (join A C)).
rewrite H.
apply (incid_A_l1l2_l1 (meet (join A C) (join B D)) (join A C) (join B D) (erefl _)).

assert (incid A (join A B)) by apply incid_x_xy.
assert (incid A (join A C)) by apply incid_x_xy.

assert (join A B == join A C).
apply a1_unique with (A:=A) (B:=(meet (join A B) (join C D))); assumption.

assert (incid A (join A B)) by apply incid_x_xy.
assert (incid B (join A B)) by apply incid_y_xy.
assert (incid C (join A B)).
move/eqP : H4 => ->.
apply incid_y_xy.
match goal with Hl :
      forall l : _, _  |- _ => 
      generalize (Hl (join A B)); intro; tauto end. 

have hmj2 :  meet (join A B) (join C D) != meet (join A D) (join B C).
apply/eqP; intro.

assert (incid (meet (join A B) (join C D)) (join A B)).
apply (incid_A_l1l2_l1 (meet (join A B) (join C D)) (join A B) (join C D) (erefl _)).
assert (incid (meet (join A B) (join C D)) (join A D)).
rewrite H.
apply (incid_A_l1l2_l1 (meet (join A D) (join B C)) (join A D) (join B C) (erefl _)).

assert (incid A (join A B)) by apply incid_x_xy.
assert (incid A (join A D)) by apply incid_x_xy.

assert (join A B == join A D).
apply a1_unique with (A:=A) (B:=(meet (join A B) (join C D))); assumption.

(*assert (incid A (join A B)) by apply incid_x_xy.*)
assert (incid B (join A B)) by apply incid_y_xy.
assert (incid D (join A B)).
move/eqP : H4 => ->.
apply incid_y_xy.
match goal with Hl :
      forall l : _, _  |- _ => 
      generalize (Hl (join A B)); intro; tauto end. 

have hmj3 : meet (join A C) (join B D) != meet (join A D) (join B C).
apply/eqP; intro.

assert (incid (meet (join A C) (join B D)) (join A C)).
apply (incid_A_l1l2_l1 (meet (join A C) (join B D)) (join A C) (join B D) (erefl _)).
assert (incid (meet (join A C) (join B D)) (join A D)).
rewrite H.
apply (incid_A_l1l2_l1 (meet (join A D) (join B C)) (join A D) (join B C) (erefl _)).

assert (incid A (join A C)) by apply incid_x_xy.
assert (incid A (join A D)) by apply incid_x_xy.

assert (join A C == join A D).
apply a1_unique with (A:=A) (B:=(meet (join A C) (join B D))); assumption.

assert (incid A (join A C)) by apply incid_x_xy.
assert (incid C (join A C)) by apply incid_y_xy.
assert (incid D (join A C)).
move/eqP : H4 => ->.
apply incid_y_xy.
match goal with Hl :
      forall l : _, _  |- _ => 
      generalize (Hl (join A C)); intro; tauto end. 

repeat rewrite cons_uniq.
rewrite /= !inE.
repeat rewrite negb_or.
by rewrite HAB HAC HAD HBC HBD HCD hA1 hA2 hA3 hB1 hB2 hB3 hC1 hC2 hC3 hD1 hD2 hD3 hmj1 hmj2 hmj3.
Qed.

Lemma at_least_7_points : 7 <= #| point |.
Proof.
  case: seven_points => A [B [C [D [E [F [G Huniq]]]]]]. 
  have hle : size[:: A; B; C; D; E; F; G] <= #|point|.
  apply/card_geqP.
  exists [::A;B;C;D;E;F;G]; by apply And3.
  by rewrite /= in hle.
Qed.

Lemma seven_lines : { l1:line & { l2 & { l3 & { l4 & { l5 & { l6 & { l7 |  
  uniq [::l1;l2;l3;l4;l5;l6;l7]}}}}}}}.
Proof.
Admitted.

Lemma at_least_7_lines : 7 <= #| line |.
Proof.
  case: seven_lines => l1 [l2 [l3 [l4 [l5 [l6 [l7 Huniq]]]]]]. 
  have hle : size[:: l1; l2; l3; l4; l5; l6; l7] <= #|line|.
  apply/card_geqP.
  exists [::l1;l2;l3;l4;l5;l6;l7]; by apply And3.
  by rewrite /= in hle.
Qed.

End min.


