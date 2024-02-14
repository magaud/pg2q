Module Type ProjectivePlane.

Parameter Point Line : Set.
Parameter Incid : Point -> Line -> Prop.

(*Parameter incid_dec : forall (A : Point)(l : Line), {Incid A l} + {~Incid A l}.*)

Parameter a1_exist : forall (A B : Point) , {l : Line | Incid A l /\ Incid B l}.

Parameter a2_exist : forall (l1 l2 : Line), {A : Point | Incid A l1 /\ Incid A l2}.

Parameter uniqueness : forall (A B : Point)(l1 l2 : Line),
  Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A = B \/ l1 = l2.

Parameter a3_1 : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A = B /\ ~ A = C /\ ~ B = C /\ Incid A l /\ Incid B l /\ Incid C l)}}}.

Parameter a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.

End ProjectivePlane.
