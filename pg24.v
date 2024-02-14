Require Import PG2X.projective_plane_axioms.

Inductive Point : Set := | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11 | P12 | P13 | P14 | P15 | P16 | P17 | P18 | P19 | P20.

Inductive Line : Set := | L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | L12 | L13 | L14 | L15 | L16 | L17 | L18 | L19 | L20.

Definition incid x l := match l with
 | L0 => match x with | P0 | P1 | P2 | P3 | P4  => true | _ => false end 
 | L1 => match x with | P0 | P5 | P6 | P7 | P8  => true | _ => false end 
 | L2 => match x with | P0 | P9 | P14 | P15 | P16  => true | _ => false end 
 | L3 => match x with | P0 | P10 | P12 | P17 | P19  => true | _ => false end 
 | L4 => match x with | P0 | P11 | P13 | P18 | P20  => true | _ => false end 
 | L5 => match x with | P1 | P5 | P9 | P10 | P11  => true | _ => false end 
 | L6 => match x with | P1 | P6 | P14 | P17 | P18  => true | _ => false end 
 | L7 => match x with | P1 | P8 | P13 | P16 | P19  => true | _ => false end 
 | L8 => match x with | P1 | P7 | P12 | P15 | P20  => true | _ => false end 
 | L9 => match x with | P2 | P5 | P14 | P19 | P20  => true | _ => false end 
 | L10 => match x with | P4 | P5 | P13 | P15 | P17  => true | _ => false end 
 | L11 => match x with | P3 | P5 | P12 | P16 | P18  => true | _ => false end 
 | L12 => match x with | P2 | P6 | P9 | P12 | P13  => true | _ => false end 
 | L13 => match x with | P2 | P7 | P11 | P16 | P17  => true | _ => false end 
 | L14 => match x with | P2 | P8 | P10 | P15 | P18  => true | _ => false end 
 | L15 => match x with | P3 | P6 | P11 | P15 | P19  => true | _ => false end 
 | L16 => match x with | P4 | P6 | P10 | P16 | P20  => true | _ => false end 
 | L17 => match x with | P4 | P7 | P9 | P18 | P19  => true | _ => false end 
 | L18 => match x with | P3 | P8 | P9 | P17 | P20  => true | _ => false end 
 | L19 => match x with | P4 | P8 | P11 | P12 | P14  => true | _ => false end 
 | L20 => match x with | P3 | P7 | P10 | P13 | P14  => true | _ => false end 
end.

Definition Incid x l := incid x l = true.

Definition l_from_points (x y:Point) := match x with
 | P0 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L1 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L2 | P10 => L3 | P11 => L4 | P12 => L3 | P13 => L4 | P14 => L2 | P15 => L2 | P16 => L2 | P17 => L3 | P18 => L4 | P19 => L3 | P20 => L4 end 
 | P1 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L5 | P6 => L6 | P7 => L8 | P8 => L7 | P9 => L5 | P10 => L5 | P11 => L5 | P12 => L8 | P13 => L7 | P14 => L6 | P15 => L8 | P16 => L7 | P17 => L6 | P18 => L6 | P19 => L7 | P20 => L8 end 
 | P2 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L9 | P6 => L12 | P7 => L13 | P8 => L14 | P9 => L12 | P10 => L14 | P11 => L13 | P12 => L12 | P13 => L12 | P14 => L9 | P15 => L14 | P16 => L13 | P17 => L13 | P18 => L14 | P19 => L9 | P20 => L9 end 
 | P3 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L11 | P6 => L15 | P7 => L20 | P8 => L18 | P9 => L18 | P10 => L20 | P11 => L15 | P12 => L11 | P13 => L20 | P14 => L20 | P15 => L15 | P16 => L11 | P17 => L18 | P18 => L11 | P19 => L15 | P20 => L18 end 
 | P4 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L10 | P6 => L16 | P7 => L17 | P8 => L19 | P9 => L17 | P10 => L16 | P11 => L19 | P12 => L19 | P13 => L10 | P14 => L19 | P15 => L10 | P16 => L16 | P17 => L10 | P18 => L17 | P19 => L17 | P20 => L16 end 
 | P5 => match y with | P0 => L1 | P1 => L5 | P2 => L9 | P3 => L11 | P4 => L10 | P5 => L1 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L5 | P10 => L5 | P11 => L5 | P12 => L11 | P13 => L10 | P14 => L9 | P15 => L10 | P16 => L11 | P17 => L10 | P18 => L11 | P19 => L9 | P20 => L9 end 
 | P6 => match y with | P0 => L1 | P1 => L6 | P2 => L12 | P3 => L15 | P4 => L16 | P5 => L1 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L12 | P10 => L16 | P11 => L15 | P12 => L12 | P13 => L12 | P14 => L6 | P15 => L15 | P16 => L16 | P17 => L6 | P18 => L6 | P19 => L15 | P20 => L16 end 
 | P7 => match y with | P0 => L1 | P1 => L8 | P2 => L13 | P3 => L20 | P4 => L17 | P5 => L1 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L17 | P10 => L20 | P11 => L13 | P12 => L8 | P13 => L20 | P14 => L20 | P15 => L8 | P16 => L13 | P17 => L13 | P18 => L17 | P19 => L17 | P20 => L8 end 
 | P8 => match y with | P0 => L1 | P1 => L7 | P2 => L14 | P3 => L18 | P4 => L19 | P5 => L1 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L18 | P10 => L14 | P11 => L19 | P12 => L19 | P13 => L7 | P14 => L19 | P15 => L14 | P16 => L7 | P17 => L18 | P18 => L14 | P19 => L7 | P20 => L18 end 
 | P9 => match y with | P0 => L2 | P1 => L5 | P2 => L12 | P3 => L18 | P4 => L17 | P5 => L5 | P6 => L12 | P7 => L17 | P8 => L18 | P9 => L2 | P10 => L5 | P11 => L5 | P12 => L12 | P13 => L12 | P14 => L2 | P15 => L2 | P16 => L2 | P17 => L18 | P18 => L17 | P19 => L17 | P20 => L18 end 
 | P10 => match y with | P0 => L3 | P1 => L5 | P2 => L14 | P3 => L20 | P4 => L16 | P5 => L5 | P6 => L16 | P7 => L20 | P8 => L14 | P9 => L5 | P10 => L3 | P11 => L5 | P12 => L3 | P13 => L20 | P14 => L20 | P15 => L14 | P16 => L16 | P17 => L3 | P18 => L14 | P19 => L3 | P20 => L16 end 
 | P11 => match y with | P0 => L4 | P1 => L5 | P2 => L13 | P3 => L15 | P4 => L19 | P5 => L5 | P6 => L15 | P7 => L13 | P8 => L19 | P9 => L5 | P10 => L5 | P11 => L4 | P12 => L19 | P13 => L4 | P14 => L19 | P15 => L15 | P16 => L13 | P17 => L13 | P18 => L4 | P19 => L15 | P20 => L4 end 
 | P12 => match y with | P0 => L3 | P1 => L8 | P2 => L12 | P3 => L11 | P4 => L19 | P5 => L11 | P6 => L12 | P7 => L8 | P8 => L19 | P9 => L12 | P10 => L3 | P11 => L19 | P12 => L3 | P13 => L12 | P14 => L19 | P15 => L8 | P16 => L11 | P17 => L3 | P18 => L11 | P19 => L3 | P20 => L8 end 
 | P13 => match y with | P0 => L4 | P1 => L7 | P2 => L12 | P3 => L20 | P4 => L10 | P5 => L10 | P6 => L12 | P7 => L20 | P8 => L7 | P9 => L12 | P10 => L20 | P11 => L4 | P12 => L12 | P13 => L4 | P14 => L20 | P15 => L10 | P16 => L7 | P17 => L10 | P18 => L4 | P19 => L7 | P20 => L4 end 
 | P14 => match y with | P0 => L2 | P1 => L6 | P2 => L9 | P3 => L20 | P4 => L19 | P5 => L9 | P6 => L6 | P7 => L20 | P8 => L19 | P9 => L2 | P10 => L20 | P11 => L19 | P12 => L19 | P13 => L20 | P14 => L2 | P15 => L2 | P16 => L2 | P17 => L6 | P18 => L6 | P19 => L9 | P20 => L9 end 
 | P15 => match y with | P0 => L2 | P1 => L8 | P2 => L14 | P3 => L15 | P4 => L10 | P5 => L10 | P6 => L15 | P7 => L8 | P8 => L14 | P9 => L2 | P10 => L14 | P11 => L15 | P12 => L8 | P13 => L10 | P14 => L2 | P15 => L2 | P16 => L2 | P17 => L10 | P18 => L14 | P19 => L15 | P20 => L8 end 
 | P16 => match y with | P0 => L2 | P1 => L7 | P2 => L13 | P3 => L11 | P4 => L16 | P5 => L11 | P6 => L16 | P7 => L13 | P8 => L7 | P9 => L2 | P10 => L16 | P11 => L13 | P12 => L11 | P13 => L7 | P14 => L2 | P15 => L2 | P16 => L2 | P17 => L13 | P18 => L11 | P19 => L7 | P20 => L16 end 
 | P17 => match y with | P0 => L3 | P1 => L6 | P2 => L13 | P3 => L18 | P4 => L10 | P5 => L10 | P6 => L6 | P7 => L13 | P8 => L18 | P9 => L18 | P10 => L3 | P11 => L13 | P12 => L3 | P13 => L10 | P14 => L6 | P15 => L10 | P16 => L13 | P17 => L3 | P18 => L6 | P19 => L3 | P20 => L18 end 
 | P18 => match y with | P0 => L4 | P1 => L6 | P2 => L14 | P3 => L11 | P4 => L17 | P5 => L11 | P6 => L6 | P7 => L17 | P8 => L14 | P9 => L17 | P10 => L14 | P11 => L4 | P12 => L11 | P13 => L4 | P14 => L6 | P15 => L14 | P16 => L11 | P17 => L6 | P18 => L4 | P19 => L17 | P20 => L4 end 
 | P19 => match y with | P0 => L3 | P1 => L7 | P2 => L9 | P3 => L15 | P4 => L17 | P5 => L9 | P6 => L15 | P7 => L17 | P8 => L7 | P9 => L17 | P10 => L3 | P11 => L15 | P12 => L3 | P13 => L7 | P14 => L9 | P15 => L15 | P16 => L7 | P17 => L3 | P18 => L17 | P19 => L3 | P20 => L9 end 
 | P20 => match y with | P0 => L4 | P1 => L8 | P2 => L9 | P3 => L18 | P4 => L16 | P5 => L9 | P6 => L16 | P7 => L8 | P8 => L18 | P9 => L18 | P10 => L16 | P11 => L4 | P12 => L8 | P13 => L4 | P14 => L9 | P15 => L8 | P16 => L16 | P17 => L18 | P18 => L4 | P19 => L9 | P20 => L4 end 
end.

Lemma a1_exist : forall (A B : Point) , {l : Line | Incid A l /\ Incid B l}.
Proof. intros A B; exists (l_from_points A B); destruct A; destruct B; exact_no_check (conj (@eq_refl bool true)(@eq_refl bool true)). Qed.

Definition p_from_lines (x y:Line) := match x with
 | L0 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P1 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P2 | L10 => P4 | L11 => P3 | L12 => P2 | L13 => P2 | L14 => P2 | L15 => P3 | L16 => P4 | L17 => P4 | L18 => P3 | L19 => P4 | L20 => P3 end 
 | L1 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P5 | L6 => P6 | L7 => P8 | L8 => P7 | L9 => P5 | L10 => P5 | L11 => P5 | L12 => P6 | L13 => P7 | L14 => P8 | L15 => P6 | L16 => P6 | L17 => P7 | L18 => P8 | L19 => P8 | L20 => P7 end 
 | L2 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P9 | L6 => P14 | L7 => P16 | L8 => P15 | L9 => P14 | L10 => P15 | L11 => P16 | L12 => P9 | L13 => P16 | L14 => P15 | L15 => P15 | L16 => P16 | L17 => P9 | L18 => P9 | L19 => P14 | L20 => P14 end 
 | L3 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P10 | L6 => P17 | L7 => P19 | L8 => P12 | L9 => P19 | L10 => P17 | L11 => P12 | L12 => P12 | L13 => P17 | L14 => P10 | L15 => P19 | L16 => P10 | L17 => P19 | L18 => P17 | L19 => P12 | L20 => P10 end 
 | L4 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P11 | L6 => P18 | L7 => P13 | L8 => P20 | L9 => P20 | L10 => P13 | L11 => P18 | L12 => P13 | L13 => P11 | L14 => P18 | L15 => P11 | L16 => P20 | L17 => P18 | L18 => P20 | L19 => P11 | L20 => P13 end 
 | L5 => match y with | L0 => P1 | L1 => P5 | L2 => P9 | L3 => P10 | L4 => P11 | L5 => P1 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P5 | L10 => P5 | L11 => P5 | L12 => P9 | L13 => P11 | L14 => P10 | L15 => P11 | L16 => P10 | L17 => P9 | L18 => P9 | L19 => P11 | L20 => P10 end 
 | L6 => match y with | L0 => P1 | L1 => P6 | L2 => P14 | L3 => P17 | L4 => P18 | L5 => P1 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P14 | L10 => P17 | L11 => P18 | L12 => P6 | L13 => P17 | L14 => P18 | L15 => P6 | L16 => P6 | L17 => P18 | L18 => P17 | L19 => P14 | L20 => P14 end 
 | L7 => match y with | L0 => P1 | L1 => P8 | L2 => P16 | L3 => P19 | L4 => P13 | L5 => P1 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P19 | L10 => P13 | L11 => P16 | L12 => P13 | L13 => P16 | L14 => P8 | L15 => P19 | L16 => P16 | L17 => P19 | L18 => P8 | L19 => P8 | L20 => P13 end 
 | L8 => match y with | L0 => P1 | L1 => P7 | L2 => P15 | L3 => P12 | L4 => P20 | L5 => P1 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P20 | L10 => P15 | L11 => P12 | L12 => P12 | L13 => P7 | L14 => P15 | L15 => P15 | L16 => P20 | L17 => P7 | L18 => P20 | L19 => P12 | L20 => P7 end 
 | L9 => match y with | L0 => P2 | L1 => P5 | L2 => P14 | L3 => P19 | L4 => P20 | L5 => P5 | L6 => P14 | L7 => P19 | L8 => P20 | L9 => P2 | L10 => P5 | L11 => P5 | L12 => P2 | L13 => P2 | L14 => P2 | L15 => P19 | L16 => P20 | L17 => P19 | L18 => P20 | L19 => P14 | L20 => P14 end 
 | L10 => match y with | L0 => P4 | L1 => P5 | L2 => P15 | L3 => P17 | L4 => P13 | L5 => P5 | L6 => P17 | L7 => P13 | L8 => P15 | L9 => P5 | L10 => P4 | L11 => P5 | L12 => P13 | L13 => P17 | L14 => P15 | L15 => P15 | L16 => P4 | L17 => P4 | L18 => P17 | L19 => P4 | L20 => P13 end 
 | L11 => match y with | L0 => P3 | L1 => P5 | L2 => P16 | L3 => P12 | L4 => P18 | L5 => P5 | L6 => P18 | L7 => P16 | L8 => P12 | L9 => P5 | L10 => P5 | L11 => P3 | L12 => P12 | L13 => P16 | L14 => P18 | L15 => P3 | L16 => P16 | L17 => P18 | L18 => P3 | L19 => P12 | L20 => P3 end 
 | L12 => match y with | L0 => P2 | L1 => P6 | L2 => P9 | L3 => P12 | L4 => P13 | L5 => P9 | L6 => P6 | L7 => P13 | L8 => P12 | L9 => P2 | L10 => P13 | L11 => P12 | L12 => P2 | L13 => P2 | L14 => P2 | L15 => P6 | L16 => P6 | L17 => P9 | L18 => P9 | L19 => P12 | L20 => P13 end 
 | L13 => match y with | L0 => P2 | L1 => P7 | L2 => P16 | L3 => P17 | L4 => P11 | L5 => P11 | L6 => P17 | L7 => P16 | L8 => P7 | L9 => P2 | L10 => P17 | L11 => P16 | L12 => P2 | L13 => P2 | L14 => P2 | L15 => P11 | L16 => P16 | L17 => P7 | L18 => P17 | L19 => P11 | L20 => P7 end 
 | L14 => match y with | L0 => P2 | L1 => P8 | L2 => P15 | L3 => P10 | L4 => P18 | L5 => P10 | L6 => P18 | L7 => P8 | L8 => P15 | L9 => P2 | L10 => P15 | L11 => P18 | L12 => P2 | L13 => P2 | L14 => P2 | L15 => P15 | L16 => P10 | L17 => P18 | L18 => P8 | L19 => P8 | L20 => P10 end 
 | L15 => match y with | L0 => P3 | L1 => P6 | L2 => P15 | L3 => P19 | L4 => P11 | L5 => P11 | L6 => P6 | L7 => P19 | L8 => P15 | L9 => P19 | L10 => P15 | L11 => P3 | L12 => P6 | L13 => P11 | L14 => P15 | L15 => P3 | L16 => P6 | L17 => P19 | L18 => P3 | L19 => P11 | L20 => P3 end 
 | L16 => match y with | L0 => P4 | L1 => P6 | L2 => P16 | L3 => P10 | L4 => P20 | L5 => P10 | L6 => P6 | L7 => P16 | L8 => P20 | L9 => P20 | L10 => P4 | L11 => P16 | L12 => P6 | L13 => P16 | L14 => P10 | L15 => P6 | L16 => P4 | L17 => P4 | L18 => P20 | L19 => P4 | L20 => P10 end 
 | L17 => match y with | L0 => P4 | L1 => P7 | L2 => P9 | L3 => P19 | L4 => P18 | L5 => P9 | L6 => P18 | L7 => P19 | L8 => P7 | L9 => P19 | L10 => P4 | L11 => P18 | L12 => P9 | L13 => P7 | L14 => P18 | L15 => P19 | L16 => P4 | L17 => P4 | L18 => P9 | L19 => P4 | L20 => P7 end 
 | L18 => match y with | L0 => P3 | L1 => P8 | L2 => P9 | L3 => P17 | L4 => P20 | L5 => P9 | L6 => P17 | L7 => P8 | L8 => P20 | L9 => P20 | L10 => P17 | L11 => P3 | L12 => P9 | L13 => P17 | L14 => P8 | L15 => P3 | L16 => P20 | L17 => P9 | L18 => P3 | L19 => P8 | L20 => P3 end 
 | L19 => match y with | L0 => P4 | L1 => P8 | L2 => P14 | L3 => P12 | L4 => P11 | L5 => P11 | L6 => P14 | L7 => P8 | L8 => P12 | L9 => P14 | L10 => P4 | L11 => P12 | L12 => P12 | L13 => P11 | L14 => P8 | L15 => P11 | L16 => P4 | L17 => P4 | L18 => P8 | L19 => P4 | L20 => P14 end 
 | L20 => match y with | L0 => P3 | L1 => P7 | L2 => P14 | L3 => P10 | L4 => P13 | L5 => P10 | L6 => P14 | L7 => P13 | L8 => P7 | L9 => P14 | L10 => P13 | L11 => P3 | L12 => P13 | L13 => P7 | L14 => P10 | L15 => P3 | L16 => P10 | L17 => P7 | L18 => P3 | L19 => P14 | L20 => P3 end 
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

Definition f_a3_1 (l:Line) := match l with | L0 => (P0,(P1,P2)) | L1 => (P0,(P5,P6)) | L2 => (P0,(P9,P14)) | L3 => (P0,(P10,P12)) | L4 => (P0,(P11,P13)) | L5 => (P1,(P5,P9)) | L6 => (P1,(P6,P14)) | L7 => (P1,(P8,P13)) | L8 => (P1,(P7,P12)) | L9 => (P2,(P5,P14)) | L10 => (P4,(P5,P13)) | L11 => (P3,(P5,P12)) | L12 => (P2,(P6,P9)) | L13 => (P2,(P7,P11)) | L14 => (P2,(P8,P10)) | L15 => (P3,(P6,P11)) | L16 => (P4,(P6,P10)) | L17 => (P4,(P7,P9)) | L18 => (P3,(P8,P9)) | L19 => (P4,(P8,P11)) | L20 => (P3,(P7,P10))end.

Lemma a3_1 : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A = B /\ ~ A = C /\ ~ B = C /\ Incid A l /\ Incid B l /\ Incid C l)}}}.
Proof.
 intros l; pose (xyz := f_a3_1 l); exists (fst xyz); exists (fst (snd xyz)); exists (snd (snd xyz)).
  destruct l; solve [split; [intro; discriminate | split; [intro; discriminate | split; [intro; discriminate | split; [reflexivity | split; reflexivity]]]]].
 Qed.

Lemma a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.
Proof. exists L1; exists L2; intro;discriminate. Qed.

Module pg24 : ProjectivePlane.

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

End pg24.

