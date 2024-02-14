Require Import PG2X.projective_plane_axioms.

Inductive Point : Set := | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11 | P12 | P13 | P14 | P15 | P16 | P17 | P18 | P19 | P20 | P21 | P22 | P23 | P24 | P25 | P26 | P27 | P28 | P29 | P30.

Inductive Line : Set := | L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | L12 | L13 | L14 | L15 | L16 | L17 | L18 | L19 | L20 | L21 | L22 | L23 | L24 | L25 | L26 | L27 | L28 | L29 | L30.

Definition incid x l := match l with
 | L0 => match x with | P0 | P1 | P2 | P3 | P4 | P5  => true | _ => false end 
 | L1 => match x with | P0 | P6 | P7 | P8 | P9 | P10  => true | _ => false end 
 | L2 => match x with | P0 | P11 | P18 | P19 | P20 | P21  => true | _ => false end 
 | L3 => match x with | P0 | P12 | P15 | P22 | P27 | P28  => true | _ => false end 
 | L4 => match x with | P0 | P13 | P16 | P24 | P26 | P30  => true | _ => false end 
 | L5 => match x with | P0 | P14 | P17 | P23 | P25 | P29  => true | _ => false end 
 | L6 => match x with | P1 | P6 | P11 | P12 | P13 | P14  => true | _ => false end 
 | L7 => match x with | P1 | P7 | P18 | P22 | P23 | P24  => true | _ => false end 
 | L8 => match x with | P1 | P8 | P16 | P19 | P27 | P29  => true | _ => false end 
 | L9 => match x with | P1 | P9 | P15 | P21 | P25 | P30  => true | _ => false end 
 | L10 => match x with | P1 | P10 | P17 | P20 | P26 | P28  => true | _ => false end 
 | L11 => match x with | P2 | P6 | P19 | P22 | P25 | P26  => true | _ => false end 
 | L12 => match x with | P3 | P6 | P17 | P18 | P27 | P30  => true | _ => false end 
 | L13 => match x with | P4 | P6 | P15 | P20 | P24 | P29  => true | _ => false end 
 | L14 => match x with | P5 | P6 | P16 | P21 | P23 | P28  => true | _ => false end 
 | L15 => match x with | P2 | P7 | P11 | P15 | P16 | P17  => true | _ => false end 
 | L16 => match x with | P2 | P9 | P13 | P18 | P28 | P29  => true | _ => false end 
 | L17 => match x with | P2 | P10 | P14 | P21 | P24 | P27  => true | _ => false end 
 | L18 => match x with | P2 | P8 | P12 | P20 | P23 | P30  => true | _ => false end 
 | L19 => match x with | P4 | P7 | P14 | P19 | P28 | P30  => true | _ => false end 
 | L20 => match x with | P5 | P7 | P13 | P20 | P25 | P27  => true | _ => false end 
 | L21 => match x with | P3 | P7 | P12 | P21 | P26 | P29  => true | _ => false end 
 | L22 => match x with | P5 | P10 | P11 | P22 | P29 | P30  => true | _ => false end 
 | L23 => match x with | P4 | P9 | P11 | P23 | P26 | P27  => true | _ => false end 
 | L24 => match x with | P3 | P8 | P11 | P24 | P25 | P28  => true | _ => false end 
 | L25 => match x with | P5 | P9 | P12 | P17 | P19 | P24  => true | _ => false end 
 | L26 => match x with | P3 | P10 | P13 | P15 | P19 | P23  => true | _ => false end 
 | L27 => match x with | P4 | P10 | P12 | P16 | P18 | P25  => true | _ => false end 
 | L28 => match x with | P5 | P8 | P14 | P15 | P18 | P26  => true | _ => false end 
 | L29 => match x with | P4 | P8 | P13 | P17 | P21 | P22  => true | _ => false end 
 | L30 => match x with | P3 | P9 | P14 | P16 | P20 | P22  => true | _ => false end 
end.

Definition Incid x l := incid x l = true.

Definition l_from_points (x y:Point) := match x with
 | P0 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L0 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L1 | P10 => L1 | P11 => L2 | P12 => L3 | P13 => L4 | P14 => L5 | P15 => L3 | P16 => L4 | P17 => L5 | P18 => L2 | P19 => L2 | P20 => L2 | P21 => L2 | P22 => L3 | P23 => L5 | P24 => L4 | P25 => L5 | P26 => L4 | P27 => L3 | P28 => L3 | P29 => L5 | P30 => L4 end 
 | P1 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L0 | P6 => L6 | P7 => L7 | P8 => L8 | P9 => L9 | P10 => L10 | P11 => L6 | P12 => L6 | P13 => L6 | P14 => L6 | P15 => L9 | P16 => L8 | P17 => L10 | P18 => L7 | P19 => L8 | P20 => L10 | P21 => L9 | P22 => L7 | P23 => L7 | P24 => L7 | P25 => L9 | P26 => L10 | P27 => L8 | P28 => L10 | P29 => L8 | P30 => L9 end 
 | P2 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L0 | P6 => L11 | P7 => L15 | P8 => L18 | P9 => L16 | P10 => L17 | P11 => L15 | P12 => L18 | P13 => L16 | P14 => L17 | P15 => L15 | P16 => L15 | P17 => L15 | P18 => L16 | P19 => L11 | P20 => L18 | P21 => L17 | P22 => L11 | P23 => L18 | P24 => L17 | P25 => L11 | P26 => L11 | P27 => L17 | P28 => L16 | P29 => L16 | P30 => L18 end 
 | P3 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L0 | P6 => L12 | P7 => L21 | P8 => L24 | P9 => L30 | P10 => L26 | P11 => L24 | P12 => L21 | P13 => L26 | P14 => L30 | P15 => L26 | P16 => L30 | P17 => L12 | P18 => L12 | P19 => L26 | P20 => L30 | P21 => L21 | P22 => L30 | P23 => L26 | P24 => L24 | P25 => L24 | P26 => L21 | P27 => L12 | P28 => L24 | P29 => L21 | P30 => L12 end 
 | P4 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L0 | P6 => L13 | P7 => L19 | P8 => L29 | P9 => L23 | P10 => L27 | P11 => L23 | P12 => L27 | P13 => L29 | P14 => L19 | P15 => L13 | P16 => L27 | P17 => L29 | P18 => L27 | P19 => L19 | P20 => L13 | P21 => L29 | P22 => L29 | P23 => L23 | P24 => L13 | P25 => L27 | P26 => L23 | P27 => L23 | P28 => L19 | P29 => L13 | P30 => L19 end 
 | P5 => match y with | P0 => L0 | P1 => L0 | P2 => L0 | P3 => L0 | P4 => L0 | P5 => L0 | P6 => L14 | P7 => L20 | P8 => L28 | P9 => L25 | P10 => L22 | P11 => L22 | P12 => L25 | P13 => L20 | P14 => L28 | P15 => L28 | P16 => L14 | P17 => L25 | P18 => L28 | P19 => L25 | P20 => L20 | P21 => L14 | P22 => L22 | P23 => L14 | P24 => L25 | P25 => L20 | P26 => L28 | P27 => L20 | P28 => L14 | P29 => L22 | P30 => L22 end 
 | P6 => match y with | P0 => L1 | P1 => L6 | P2 => L11 | P3 => L12 | P4 => L13 | P5 => L14 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L1 | P10 => L1 | P11 => L6 | P12 => L6 | P13 => L6 | P14 => L6 | P15 => L13 | P16 => L14 | P17 => L12 | P18 => L12 | P19 => L11 | P20 => L13 | P21 => L14 | P22 => L11 | P23 => L14 | P24 => L13 | P25 => L11 | P26 => L11 | P27 => L12 | P28 => L14 | P29 => L13 | P30 => L12 end 
 | P7 => match y with | P0 => L1 | P1 => L7 | P2 => L15 | P3 => L21 | P4 => L19 | P5 => L20 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L1 | P10 => L1 | P11 => L15 | P12 => L21 | P13 => L20 | P14 => L19 | P15 => L15 | P16 => L15 | P17 => L15 | P18 => L7 | P19 => L19 | P20 => L20 | P21 => L21 | P22 => L7 | P23 => L7 | P24 => L7 | P25 => L20 | P26 => L21 | P27 => L20 | P28 => L19 | P29 => L21 | P30 => L19 end 
 | P8 => match y with | P0 => L1 | P1 => L8 | P2 => L18 | P3 => L24 | P4 => L29 | P5 => L28 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L1 | P10 => L1 | P11 => L24 | P12 => L18 | P13 => L29 | P14 => L28 | P15 => L28 | P16 => L8 | P17 => L29 | P18 => L28 | P19 => L8 | P20 => L18 | P21 => L29 | P22 => L29 | P23 => L18 | P24 => L24 | P25 => L24 | P26 => L28 | P27 => L8 | P28 => L24 | P29 => L8 | P30 => L18 end 
 | P9 => match y with | P0 => L1 | P1 => L9 | P2 => L16 | P3 => L30 | P4 => L23 | P5 => L25 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L1 | P10 => L1 | P11 => L23 | P12 => L25 | P13 => L16 | P14 => L30 | P15 => L9 | P16 => L30 | P17 => L25 | P18 => L16 | P19 => L25 | P20 => L30 | P21 => L9 | P22 => L30 | P23 => L23 | P24 => L25 | P25 => L9 | P26 => L23 | P27 => L23 | P28 => L16 | P29 => L16 | P30 => L9 end 
 | P10 => match y with | P0 => L1 | P1 => L10 | P2 => L17 | P3 => L26 | P4 => L27 | P5 => L22 | P6 => L1 | P7 => L1 | P8 => L1 | P9 => L1 | P10 => L1 | P11 => L22 | P12 => L27 | P13 => L26 | P14 => L17 | P15 => L26 | P16 => L27 | P17 => L10 | P18 => L27 | P19 => L26 | P20 => L10 | P21 => L17 | P22 => L22 | P23 => L26 | P24 => L17 | P25 => L27 | P26 => L10 | P27 => L17 | P28 => L10 | P29 => L22 | P30 => L22 end 
 | P11 => match y with | P0 => L2 | P1 => L6 | P2 => L15 | P3 => L24 | P4 => L23 | P5 => L22 | P6 => L6 | P7 => L15 | P8 => L24 | P9 => L23 | P10 => L22 | P11 => L2 | P12 => L6 | P13 => L6 | P14 => L6 | P15 => L15 | P16 => L15 | P17 => L15 | P18 => L2 | P19 => L2 | P20 => L2 | P21 => L2 | P22 => L22 | P23 => L23 | P24 => L24 | P25 => L24 | P26 => L23 | P27 => L23 | P28 => L24 | P29 => L22 | P30 => L22 end 
 | P12 => match y with | P0 => L3 | P1 => L6 | P2 => L18 | P3 => L21 | P4 => L27 | P5 => L25 | P6 => L6 | P7 => L21 | P8 => L18 | P9 => L25 | P10 => L27 | P11 => L6 | P12 => L3 | P13 => L6 | P14 => L6 | P15 => L3 | P16 => L27 | P17 => L25 | P18 => L27 | P19 => L25 | P20 => L18 | P21 => L21 | P22 => L3 | P23 => L18 | P24 => L25 | P25 => L27 | P26 => L21 | P27 => L3 | P28 => L3 | P29 => L21 | P30 => L18 end 
 | P13 => match y with | P0 => L4 | P1 => L6 | P2 => L16 | P3 => L26 | P4 => L29 | P5 => L20 | P6 => L6 | P7 => L20 | P8 => L29 | P9 => L16 | P10 => L26 | P11 => L6 | P12 => L6 | P13 => L4 | P14 => L6 | P15 => L26 | P16 => L4 | P17 => L29 | P18 => L16 | P19 => L26 | P20 => L20 | P21 => L29 | P22 => L29 | P23 => L26 | P24 => L4 | P25 => L20 | P26 => L4 | P27 => L20 | P28 => L16 | P29 => L16 | P30 => L4 end 
 | P14 => match y with | P0 => L5 | P1 => L6 | P2 => L17 | P3 => L30 | P4 => L19 | P5 => L28 | P6 => L6 | P7 => L19 | P8 => L28 | P9 => L30 | P10 => L17 | P11 => L6 | P12 => L6 | P13 => L6 | P14 => L5 | P15 => L28 | P16 => L30 | P17 => L5 | P18 => L28 | P19 => L19 | P20 => L30 | P21 => L17 | P22 => L30 | P23 => L5 | P24 => L17 | P25 => L5 | P26 => L28 | P27 => L17 | P28 => L19 | P29 => L5 | P30 => L19 end 
 | P15 => match y with | P0 => L3 | P1 => L9 | P2 => L15 | P3 => L26 | P4 => L13 | P5 => L28 | P6 => L13 | P7 => L15 | P8 => L28 | P9 => L9 | P10 => L26 | P11 => L15 | P12 => L3 | P13 => L26 | P14 => L28 | P15 => L3 | P16 => L15 | P17 => L15 | P18 => L28 | P19 => L26 | P20 => L13 | P21 => L9 | P22 => L3 | P23 => L26 | P24 => L13 | P25 => L9 | P26 => L28 | P27 => L3 | P28 => L3 | P29 => L13 | P30 => L9 end 
 | P16 => match y with | P0 => L4 | P1 => L8 | P2 => L15 | P3 => L30 | P4 => L27 | P5 => L14 | P6 => L14 | P7 => L15 | P8 => L8 | P9 => L30 | P10 => L27 | P11 => L15 | P12 => L27 | P13 => L4 | P14 => L30 | P15 => L15 | P16 => L4 | P17 => L15 | P18 => L27 | P19 => L8 | P20 => L30 | P21 => L14 | P22 => L30 | P23 => L14 | P24 => L4 | P25 => L27 | P26 => L4 | P27 => L8 | P28 => L14 | P29 => L8 | P30 => L4 end 
 | P17 => match y with | P0 => L5 | P1 => L10 | P2 => L15 | P3 => L12 | P4 => L29 | P5 => L25 | P6 => L12 | P7 => L15 | P8 => L29 | P9 => L25 | P10 => L10 | P11 => L15 | P12 => L25 | P13 => L29 | P14 => L5 | P15 => L15 | P16 => L15 | P17 => L5 | P18 => L12 | P19 => L25 | P20 => L10 | P21 => L29 | P22 => L29 | P23 => L5 | P24 => L25 | P25 => L5 | P26 => L10 | P27 => L12 | P28 => L10 | P29 => L5 | P30 => L12 end 
 | P18 => match y with | P0 => L2 | P1 => L7 | P2 => L16 | P3 => L12 | P4 => L27 | P5 => L28 | P6 => L12 | P7 => L7 | P8 => L28 | P9 => L16 | P10 => L27 | P11 => L2 | P12 => L27 | P13 => L16 | P14 => L28 | P15 => L28 | P16 => L27 | P17 => L12 | P18 => L2 | P19 => L2 | P20 => L2 | P21 => L2 | P22 => L7 | P23 => L7 | P24 => L7 | P25 => L27 | P26 => L28 | P27 => L12 | P28 => L16 | P29 => L16 | P30 => L12 end 
 | P19 => match y with | P0 => L2 | P1 => L8 | P2 => L11 | P3 => L26 | P4 => L19 | P5 => L25 | P6 => L11 | P7 => L19 | P8 => L8 | P9 => L25 | P10 => L26 | P11 => L2 | P12 => L25 | P13 => L26 | P14 => L19 | P15 => L26 | P16 => L8 | P17 => L25 | P18 => L2 | P19 => L2 | P20 => L2 | P21 => L2 | P22 => L11 | P23 => L26 | P24 => L25 | P25 => L11 | P26 => L11 | P27 => L8 | P28 => L19 | P29 => L8 | P30 => L19 end 
 | P20 => match y with | P0 => L2 | P1 => L10 | P2 => L18 | P3 => L30 | P4 => L13 | P5 => L20 | P6 => L13 | P7 => L20 | P8 => L18 | P9 => L30 | P10 => L10 | P11 => L2 | P12 => L18 | P13 => L20 | P14 => L30 | P15 => L13 | P16 => L30 | P17 => L10 | P18 => L2 | P19 => L2 | P20 => L2 | P21 => L2 | P22 => L30 | P23 => L18 | P24 => L13 | P25 => L20 | P26 => L10 | P27 => L20 | P28 => L10 | P29 => L13 | P30 => L18 end 
 | P21 => match y with | P0 => L2 | P1 => L9 | P2 => L17 | P3 => L21 | P4 => L29 | P5 => L14 | P6 => L14 | P7 => L21 | P8 => L29 | P9 => L9 | P10 => L17 | P11 => L2 | P12 => L21 | P13 => L29 | P14 => L17 | P15 => L9 | P16 => L14 | P17 => L29 | P18 => L2 | P19 => L2 | P20 => L2 | P21 => L2 | P22 => L29 | P23 => L14 | P24 => L17 | P25 => L9 | P26 => L21 | P27 => L17 | P28 => L14 | P29 => L21 | P30 => L9 end 
 | P22 => match y with | P0 => L3 | P1 => L7 | P2 => L11 | P3 => L30 | P4 => L29 | P5 => L22 | P6 => L11 | P7 => L7 | P8 => L29 | P9 => L30 | P10 => L22 | P11 => L22 | P12 => L3 | P13 => L29 | P14 => L30 | P15 => L3 | P16 => L30 | P17 => L29 | P18 => L7 | P19 => L11 | P20 => L30 | P21 => L29 | P22 => L3 | P23 => L7 | P24 => L7 | P25 => L11 | P26 => L11 | P27 => L3 | P28 => L3 | P29 => L22 | P30 => L22 end 
 | P23 => match y with | P0 => L5 | P1 => L7 | P2 => L18 | P3 => L26 | P4 => L23 | P5 => L14 | P6 => L14 | P7 => L7 | P8 => L18 | P9 => L23 | P10 => L26 | P11 => L23 | P12 => L18 | P13 => L26 | P14 => L5 | P15 => L26 | P16 => L14 | P17 => L5 | P18 => L7 | P19 => L26 | P20 => L18 | P21 => L14 | P22 => L7 | P23 => L5 | P24 => L7 | P25 => L5 | P26 => L23 | P27 => L23 | P28 => L14 | P29 => L5 | P30 => L18 end 
 | P24 => match y with | P0 => L4 | P1 => L7 | P2 => L17 | P3 => L24 | P4 => L13 | P5 => L25 | P6 => L13 | P7 => L7 | P8 => L24 | P9 => L25 | P10 => L17 | P11 => L24 | P12 => L25 | P13 => L4 | P14 => L17 | P15 => L13 | P16 => L4 | P17 => L25 | P18 => L7 | P19 => L25 | P20 => L13 | P21 => L17 | P22 => L7 | P23 => L7 | P24 => L4 | P25 => L24 | P26 => L4 | P27 => L17 | P28 => L24 | P29 => L13 | P30 => L4 end 
 | P25 => match y with | P0 => L5 | P1 => L9 | P2 => L11 | P3 => L24 | P4 => L27 | P5 => L20 | P6 => L11 | P7 => L20 | P8 => L24 | P9 => L9 | P10 => L27 | P11 => L24 | P12 => L27 | P13 => L20 | P14 => L5 | P15 => L9 | P16 => L27 | P17 => L5 | P18 => L27 | P19 => L11 | P20 => L20 | P21 => L9 | P22 => L11 | P23 => L5 | P24 => L24 | P25 => L5 | P26 => L11 | P27 => L20 | P28 => L24 | P29 => L5 | P30 => L9 end 
 | P26 => match y with | P0 => L4 | P1 => L10 | P2 => L11 | P3 => L21 | P4 => L23 | P5 => L28 | P6 => L11 | P7 => L21 | P8 => L28 | P9 => L23 | P10 => L10 | P11 => L23 | P12 => L21 | P13 => L4 | P14 => L28 | P15 => L28 | P16 => L4 | P17 => L10 | P18 => L28 | P19 => L11 | P20 => L10 | P21 => L21 | P22 => L11 | P23 => L23 | P24 => L4 | P25 => L11 | P26 => L4 | P27 => L23 | P28 => L10 | P29 => L21 | P30 => L4 end 
 | P27 => match y with | P0 => L3 | P1 => L8 | P2 => L17 | P3 => L12 | P4 => L23 | P5 => L20 | P6 => L12 | P7 => L20 | P8 => L8 | P9 => L23 | P10 => L17 | P11 => L23 | P12 => L3 | P13 => L20 | P14 => L17 | P15 => L3 | P16 => L8 | P17 => L12 | P18 => L12 | P19 => L8 | P20 => L20 | P21 => L17 | P22 => L3 | P23 => L23 | P24 => L17 | P25 => L20 | P26 => L23 | P27 => L3 | P28 => L3 | P29 => L8 | P30 => L12 end 
 | P28 => match y with | P0 => L3 | P1 => L10 | P2 => L16 | P3 => L24 | P4 => L19 | P5 => L14 | P6 => L14 | P7 => L19 | P8 => L24 | P9 => L16 | P10 => L10 | P11 => L24 | P12 => L3 | P13 => L16 | P14 => L19 | P15 => L3 | P16 => L14 | P17 => L10 | P18 => L16 | P19 => L19 | P20 => L10 | P21 => L14 | P22 => L3 | P23 => L14 | P24 => L24 | P25 => L24 | P26 => L10 | P27 => L3 | P28 => L3 | P29 => L16 | P30 => L19 end 
 | P29 => match y with | P0 => L5 | P1 => L8 | P2 => L16 | P3 => L21 | P4 => L13 | P5 => L22 | P6 => L13 | P7 => L21 | P8 => L8 | P9 => L16 | P10 => L22 | P11 => L22 | P12 => L21 | P13 => L16 | P14 => L5 | P15 => L13 | P16 => L8 | P17 => L5 | P18 => L16 | P19 => L8 | P20 => L13 | P21 => L21 | P22 => L22 | P23 => L5 | P24 => L13 | P25 => L5 | P26 => L21 | P27 => L8 | P28 => L16 | P29 => L5 | P30 => L22 end 
 | P30 => match y with | P0 => L4 | P1 => L9 | P2 => L18 | P3 => L12 | P4 => L19 | P5 => L22 | P6 => L12 | P7 => L19 | P8 => L18 | P9 => L9 | P10 => L22 | P11 => L22 | P12 => L18 | P13 => L4 | P14 => L19 | P15 => L9 | P16 => L4 | P17 => L12 | P18 => L12 | P19 => L19 | P20 => L18 | P21 => L9 | P22 => L22 | P23 => L18 | P24 => L4 | P25 => L9 | P26 => L4 | P27 => L12 | P28 => L19 | P29 => L22 | P30 => L4 end 
end.

Lemma a1_exist : forall (A B : Point) , {l : Line | Incid A l /\ Incid B l}.
Proof. intros A B; exists (l_from_points A B); destruct A; destruct B; exact_no_check (conj (@eq_refl bool true)(@eq_refl bool true)). Qed.

Definition p_from_lines (x y:Line) := match x with
 | L0 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P0 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P1 | L10 => P1 | L11 => P2 | L12 => P3 | L13 => P4 | L14 => P5 | L15 => P2 | L16 => P2 | L17 => P2 | L18 => P2 | L19 => P4 | L20 => P5 | L21 => P3 | L22 => P5 | L23 => P4 | L24 => P3 | L25 => P5 | L26 => P3 | L27 => P4 | L28 => P5 | L29 => P4 | L30 => P3 end 
 | L1 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P0 | L6 => P6 | L7 => P7 | L8 => P8 | L9 => P9 | L10 => P10 | L11 => P6 | L12 => P6 | L13 => P6 | L14 => P6 | L15 => P7 | L16 => P9 | L17 => P10 | L18 => P8 | L19 => P7 | L20 => P7 | L21 => P7 | L22 => P10 | L23 => P9 | L24 => P8 | L25 => P9 | L26 => P10 | L27 => P10 | L28 => P8 | L29 => P8 | L30 => P9 end 
 | L2 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P0 | L6 => P11 | L7 => P18 | L8 => P19 | L9 => P21 | L10 => P20 | L11 => P19 | L12 => P18 | L13 => P20 | L14 => P21 | L15 => P11 | L16 => P18 | L17 => P21 | L18 => P20 | L19 => P19 | L20 => P20 | L21 => P21 | L22 => P11 | L23 => P11 | L24 => P11 | L25 => P19 | L26 => P19 | L27 => P18 | L28 => P18 | L29 => P21 | L30 => P20 end 
 | L3 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P0 | L6 => P12 | L7 => P22 | L8 => P27 | L9 => P15 | L10 => P28 | L11 => P22 | L12 => P27 | L13 => P15 | L14 => P28 | L15 => P15 | L16 => P28 | L17 => P27 | L18 => P12 | L19 => P28 | L20 => P27 | L21 => P12 | L22 => P22 | L23 => P27 | L24 => P28 | L25 => P12 | L26 => P15 | L27 => P12 | L28 => P15 | L29 => P22 | L30 => P22 end 
 | L4 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P0 | L6 => P13 | L7 => P24 | L8 => P16 | L9 => P30 | L10 => P26 | L11 => P26 | L12 => P30 | L13 => P24 | L14 => P16 | L15 => P16 | L16 => P13 | L17 => P24 | L18 => P30 | L19 => P30 | L20 => P13 | L21 => P26 | L22 => P30 | L23 => P26 | L24 => P24 | L25 => P24 | L26 => P13 | L27 => P16 | L28 => P26 | L29 => P13 | L30 => P16 end 
 | L5 => match y with | L0 => P0 | L1 => P0 | L2 => P0 | L3 => P0 | L4 => P0 | L5 => P0 | L6 => P14 | L7 => P23 | L8 => P29 | L9 => P25 | L10 => P17 | L11 => P25 | L12 => P17 | L13 => P29 | L14 => P23 | L15 => P17 | L16 => P29 | L17 => P14 | L18 => P23 | L19 => P14 | L20 => P25 | L21 => P29 | L22 => P29 | L23 => P23 | L24 => P25 | L25 => P17 | L26 => P23 | L27 => P25 | L28 => P14 | L29 => P17 | L30 => P14 end 
 | L6 => match y with | L0 => P1 | L1 => P6 | L2 => P11 | L3 => P12 | L4 => P13 | L5 => P14 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P1 | L10 => P1 | L11 => P6 | L12 => P6 | L13 => P6 | L14 => P6 | L15 => P11 | L16 => P13 | L17 => P14 | L18 => P12 | L19 => P14 | L20 => P13 | L21 => P12 | L22 => P11 | L23 => P11 | L24 => P11 | L25 => P12 | L26 => P13 | L27 => P12 | L28 => P14 | L29 => P13 | L30 => P14 end 
 | L7 => match y with | L0 => P1 | L1 => P7 | L2 => P18 | L3 => P22 | L4 => P24 | L5 => P23 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P1 | L10 => P1 | L11 => P22 | L12 => P18 | L13 => P24 | L14 => P23 | L15 => P7 | L16 => P18 | L17 => P24 | L18 => P23 | L19 => P7 | L20 => P7 | L21 => P7 | L22 => P22 | L23 => P23 | L24 => P24 | L25 => P24 | L26 => P23 | L27 => P18 | L28 => P18 | L29 => P22 | L30 => P22 end 
 | L8 => match y with | L0 => P1 | L1 => P8 | L2 => P19 | L3 => P27 | L4 => P16 | L5 => P29 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P1 | L10 => P1 | L11 => P19 | L12 => P27 | L13 => P29 | L14 => P16 | L15 => P16 | L16 => P29 | L17 => P27 | L18 => P8 | L19 => P19 | L20 => P27 | L21 => P29 | L22 => P29 | L23 => P27 | L24 => P8 | L25 => P19 | L26 => P19 | L27 => P16 | L28 => P8 | L29 => P8 | L30 => P16 end 
 | L9 => match y with | L0 => P1 | L1 => P9 | L2 => P21 | L3 => P15 | L4 => P30 | L5 => P25 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P1 | L10 => P1 | L11 => P25 | L12 => P30 | L13 => P15 | L14 => P21 | L15 => P15 | L16 => P9 | L17 => P21 | L18 => P30 | L19 => P30 | L20 => P25 | L21 => P21 | L22 => P30 | L23 => P9 | L24 => P25 | L25 => P9 | L26 => P15 | L27 => P25 | L28 => P15 | L29 => P21 | L30 => P9 end 
 | L10 => match y with | L0 => P1 | L1 => P10 | L2 => P20 | L3 => P28 | L4 => P26 | L5 => P17 | L6 => P1 | L7 => P1 | L8 => P1 | L9 => P1 | L10 => P1 | L11 => P26 | L12 => P17 | L13 => P20 | L14 => P28 | L15 => P17 | L16 => P28 | L17 => P10 | L18 => P20 | L19 => P28 | L20 => P20 | L21 => P26 | L22 => P10 | L23 => P26 | L24 => P28 | L25 => P17 | L26 => P10 | L27 => P10 | L28 => P26 | L29 => P17 | L30 => P20 end 
 | L11 => match y with | L0 => P2 | L1 => P6 | L2 => P19 | L3 => P22 | L4 => P26 | L5 => P25 | L6 => P6 | L7 => P22 | L8 => P19 | L9 => P25 | L10 => P26 | L11 => P2 | L12 => P6 | L13 => P6 | L14 => P6 | L15 => P2 | L16 => P2 | L17 => P2 | L18 => P2 | L19 => P19 | L20 => P25 | L21 => P26 | L22 => P22 | L23 => P26 | L24 => P25 | L25 => P19 | L26 => P19 | L27 => P25 | L28 => P26 | L29 => P22 | L30 => P22 end 
 | L12 => match y with | L0 => P3 | L1 => P6 | L2 => P18 | L3 => P27 | L4 => P30 | L5 => P17 | L6 => P6 | L7 => P18 | L8 => P27 | L9 => P30 | L10 => P17 | L11 => P6 | L12 => P3 | L13 => P6 | L14 => P6 | L15 => P17 | L16 => P18 | L17 => P27 | L18 => P30 | L19 => P30 | L20 => P27 | L21 => P3 | L22 => P30 | L23 => P27 | L24 => P3 | L25 => P17 | L26 => P3 | L27 => P18 | L28 => P18 | L29 => P17 | L30 => P3 end 
 | L13 => match y with | L0 => P4 | L1 => P6 | L2 => P20 | L3 => P15 | L4 => P24 | L5 => P29 | L6 => P6 | L7 => P24 | L8 => P29 | L9 => P15 | L10 => P20 | L11 => P6 | L12 => P6 | L13 => P4 | L14 => P6 | L15 => P15 | L16 => P29 | L17 => P24 | L18 => P20 | L19 => P4 | L20 => P20 | L21 => P29 | L22 => P29 | L23 => P4 | L24 => P24 | L25 => P24 | L26 => P15 | L27 => P4 | L28 => P15 | L29 => P4 | L30 => P20 end 
 | L14 => match y with | L0 => P5 | L1 => P6 | L2 => P21 | L3 => P28 | L4 => P16 | L5 => P23 | L6 => P6 | L7 => P23 | L8 => P16 | L9 => P21 | L10 => P28 | L11 => P6 | L12 => P6 | L13 => P6 | L14 => P5 | L15 => P16 | L16 => P28 | L17 => P21 | L18 => P23 | L19 => P28 | L20 => P5 | L21 => P21 | L22 => P5 | L23 => P23 | L24 => P28 | L25 => P5 | L26 => P23 | L27 => P16 | L28 => P5 | L29 => P21 | L30 => P16 end 
 | L15 => match y with | L0 => P2 | L1 => P7 | L2 => P11 | L3 => P15 | L4 => P16 | L5 => P17 | L6 => P11 | L7 => P7 | L8 => P16 | L9 => P15 | L10 => P17 | L11 => P2 | L12 => P17 | L13 => P15 | L14 => P16 | L15 => P2 | L16 => P2 | L17 => P2 | L18 => P2 | L19 => P7 | L20 => P7 | L21 => P7 | L22 => P11 | L23 => P11 | L24 => P11 | L25 => P17 | L26 => P15 | L27 => P16 | L28 => P15 | L29 => P17 | L30 => P16 end 
 | L16 => match y with | L0 => P2 | L1 => P9 | L2 => P18 | L3 => P28 | L4 => P13 | L5 => P29 | L6 => P13 | L7 => P18 | L8 => P29 | L9 => P9 | L10 => P28 | L11 => P2 | L12 => P18 | L13 => P29 | L14 => P28 | L15 => P2 | L16 => P2 | L17 => P2 | L18 => P2 | L19 => P28 | L20 => P13 | L21 => P29 | L22 => P29 | L23 => P9 | L24 => P28 | L25 => P9 | L26 => P13 | L27 => P18 | L28 => P18 | L29 => P13 | L30 => P9 end 
 | L17 => match y with | L0 => P2 | L1 => P10 | L2 => P21 | L3 => P27 | L4 => P24 | L5 => P14 | L6 => P14 | L7 => P24 | L8 => P27 | L9 => P21 | L10 => P10 | L11 => P2 | L12 => P27 | L13 => P24 | L14 => P21 | L15 => P2 | L16 => P2 | L17 => P2 | L18 => P2 | L19 => P14 | L20 => P27 | L21 => P21 | L22 => P10 | L23 => P27 | L24 => P24 | L25 => P24 | L26 => P10 | L27 => P10 | L28 => P14 | L29 => P21 | L30 => P14 end 
 | L18 => match y with | L0 => P2 | L1 => P8 | L2 => P20 | L3 => P12 | L4 => P30 | L5 => P23 | L6 => P12 | L7 => P23 | L8 => P8 | L9 => P30 | L10 => P20 | L11 => P2 | L12 => P30 | L13 => P20 | L14 => P23 | L15 => P2 | L16 => P2 | L17 => P2 | L18 => P2 | L19 => P30 | L20 => P20 | L21 => P12 | L22 => P30 | L23 => P23 | L24 => P8 | L25 => P12 | L26 => P23 | L27 => P12 | L28 => P8 | L29 => P8 | L30 => P20 end 
 | L19 => match y with | L0 => P4 | L1 => P7 | L2 => P19 | L3 => P28 | L4 => P30 | L5 => P14 | L6 => P14 | L7 => P7 | L8 => P19 | L9 => P30 | L10 => P28 | L11 => P19 | L12 => P30 | L13 => P4 | L14 => P28 | L15 => P7 | L16 => P28 | L17 => P14 | L18 => P30 | L19 => P4 | L20 => P7 | L21 => P7 | L22 => P30 | L23 => P4 | L24 => P28 | L25 => P19 | L26 => P19 | L27 => P4 | L28 => P14 | L29 => P4 | L30 => P14 end 
 | L20 => match y with | L0 => P5 | L1 => P7 | L2 => P20 | L3 => P27 | L4 => P13 | L5 => P25 | L6 => P13 | L7 => P7 | L8 => P27 | L9 => P25 | L10 => P20 | L11 => P25 | L12 => P27 | L13 => P20 | L14 => P5 | L15 => P7 | L16 => P13 | L17 => P27 | L18 => P20 | L19 => P7 | L20 => P5 | L21 => P7 | L22 => P5 | L23 => P27 | L24 => P25 | L25 => P5 | L26 => P13 | L27 => P25 | L28 => P5 | L29 => P13 | L30 => P20 end 
 | L21 => match y with | L0 => P3 | L1 => P7 | L2 => P21 | L3 => P12 | L4 => P26 | L5 => P29 | L6 => P12 | L7 => P7 | L8 => P29 | L9 => P21 | L10 => P26 | L11 => P26 | L12 => P3 | L13 => P29 | L14 => P21 | L15 => P7 | L16 => P29 | L17 => P21 | L18 => P12 | L19 => P7 | L20 => P7 | L21 => P3 | L22 => P29 | L23 => P26 | L24 => P3 | L25 => P12 | L26 => P3 | L27 => P12 | L28 => P26 | L29 => P21 | L30 => P3 end 
 | L22 => match y with | L0 => P5 | L1 => P10 | L2 => P11 | L3 => P22 | L4 => P30 | L5 => P29 | L6 => P11 | L7 => P22 | L8 => P29 | L9 => P30 | L10 => P10 | L11 => P22 | L12 => P30 | L13 => P29 | L14 => P5 | L15 => P11 | L16 => P29 | L17 => P10 | L18 => P30 | L19 => P30 | L20 => P5 | L21 => P29 | L22 => P5 | L23 => P11 | L24 => P11 | L25 => P5 | L26 => P10 | L27 => P10 | L28 => P5 | L29 => P22 | L30 => P22 end 
 | L23 => match y with | L0 => P4 | L1 => P9 | L2 => P11 | L3 => P27 | L4 => P26 | L5 => P23 | L6 => P11 | L7 => P23 | L8 => P27 | L9 => P9 | L10 => P26 | L11 => P26 | L12 => P27 | L13 => P4 | L14 => P23 | L15 => P11 | L16 => P9 | L17 => P27 | L18 => P23 | L19 => P4 | L20 => P27 | L21 => P26 | L22 => P11 | L23 => P4 | L24 => P11 | L25 => P9 | L26 => P23 | L27 => P4 | L28 => P26 | L29 => P4 | L30 => P9 end 
 | L24 => match y with | L0 => P3 | L1 => P8 | L2 => P11 | L3 => P28 | L4 => P24 | L5 => P25 | L6 => P11 | L7 => P24 | L8 => P8 | L9 => P25 | L10 => P28 | L11 => P25 | L12 => P3 | L13 => P24 | L14 => P28 | L15 => P11 | L16 => P28 | L17 => P24 | L18 => P8 | L19 => P28 | L20 => P25 | L21 => P3 | L22 => P11 | L23 => P11 | L24 => P3 | L25 => P24 | L26 => P3 | L27 => P25 | L28 => P8 | L29 => P8 | L30 => P3 end 
 | L25 => match y with | L0 => P5 | L1 => P9 | L2 => P19 | L3 => P12 | L4 => P24 | L5 => P17 | L6 => P12 | L7 => P24 | L8 => P19 | L9 => P9 | L10 => P17 | L11 => P19 | L12 => P17 | L13 => P24 | L14 => P5 | L15 => P17 | L16 => P9 | L17 => P24 | L18 => P12 | L19 => P19 | L20 => P5 | L21 => P12 | L22 => P5 | L23 => P9 | L24 => P24 | L25 => P5 | L26 => P19 | L27 => P12 | L28 => P5 | L29 => P17 | L30 => P9 end 
 | L26 => match y with | L0 => P3 | L1 => P10 | L2 => P19 | L3 => P15 | L4 => P13 | L5 => P23 | L6 => P13 | L7 => P23 | L8 => P19 | L9 => P15 | L10 => P10 | L11 => P19 | L12 => P3 | L13 => P15 | L14 => P23 | L15 => P15 | L16 => P13 | L17 => P10 | L18 => P23 | L19 => P19 | L20 => P13 | L21 => P3 | L22 => P10 | L23 => P23 | L24 => P3 | L25 => P19 | L26 => P3 | L27 => P10 | L28 => P15 | L29 => P13 | L30 => P3 end 
 | L27 => match y with | L0 => P4 | L1 => P10 | L2 => P18 | L3 => P12 | L4 => P16 | L5 => P25 | L6 => P12 | L7 => P18 | L8 => P16 | L9 => P25 | L10 => P10 | L11 => P25 | L12 => P18 | L13 => P4 | L14 => P16 | L15 => P16 | L16 => P18 | L17 => P10 | L18 => P12 | L19 => P4 | L20 => P25 | L21 => P12 | L22 => P10 | L23 => P4 | L24 => P25 | L25 => P12 | L26 => P10 | L27 => P4 | L28 => P18 | L29 => P4 | L30 => P16 end 
 | L28 => match y with | L0 => P5 | L1 => P8 | L2 => P18 | L3 => P15 | L4 => P26 | L5 => P14 | L6 => P14 | L7 => P18 | L8 => P8 | L9 => P15 | L10 => P26 | L11 => P26 | L12 => P18 | L13 => P15 | L14 => P5 | L15 => P15 | L16 => P18 | L17 => P14 | L18 => P8 | L19 => P14 | L20 => P5 | L21 => P26 | L22 => P5 | L23 => P26 | L24 => P8 | L25 => P5 | L26 => P15 | L27 => P18 | L28 => P5 | L29 => P8 | L30 => P14 end 
 | L29 => match y with | L0 => P4 | L1 => P8 | L2 => P21 | L3 => P22 | L4 => P13 | L5 => P17 | L6 => P13 | L7 => P22 | L8 => P8 | L9 => P21 | L10 => P17 | L11 => P22 | L12 => P17 | L13 => P4 | L14 => P21 | L15 => P17 | L16 => P13 | L17 => P21 | L18 => P8 | L19 => P4 | L20 => P13 | L21 => P21 | L22 => P22 | L23 => P4 | L24 => P8 | L25 => P17 | L26 => P13 | L27 => P4 | L28 => P8 | L29 => P4 | L30 => P22 end 
 | L30 => match y with | L0 => P3 | L1 => P9 | L2 => P20 | L3 => P22 | L4 => P16 | L5 => P14 | L6 => P14 | L7 => P22 | L8 => P16 | L9 => P9 | L10 => P20 | L11 => P22 | L12 => P3 | L13 => P20 | L14 => P16 | L15 => P16 | L16 => P9 | L17 => P14 | L18 => P20 | L19 => P14 | L20 => P20 | L21 => P3 | L22 => P22 | L23 => P9 | L24 => P3 | L25 => P9 | L26 => P3 | L27 => P16 | L28 => P14 | L29 => P22 | L30 => P3 end 
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

Definition f_a3_1 (l:Line) := match l with | L0 => (P0,(P1,P2)) | L1 => (P0,(P6,P7)) | L2 => (P0,(P11,P18)) | L3 => (P0,(P12,P15)) | L4 => (P0,(P13,P16)) | L5 => (P0,(P14,P17)) | L6 => (P1,(P6,P11)) | L7 => (P1,(P7,P18)) | L8 => (P1,(P8,P16)) | L9 => (P1,(P9,P15)) | L10 => (P1,(P10,P17)) | L11 => (P2,(P6,P19)) | L12 => (P3,(P6,P17)) | L13 => (P4,(P6,P15)) | L14 => (P5,(P6,P16)) | L15 => (P2,(P7,P11)) | L16 => (P2,(P9,P13)) | L17 => (P2,(P10,P14)) | L18 => (P2,(P8,P12)) | L19 => (P4,(P7,P14)) | L20 => (P5,(P7,P13)) | L21 => (P3,(P7,P12)) | L22 => (P5,(P10,P11)) | L23 => (P4,(P9,P11)) | L24 => (P3,(P8,P11)) | L25 => (P5,(P9,P12)) | L26 => (P3,(P10,P13)) | L27 => (P4,(P10,P12)) | L28 => (P5,(P8,P14)) | L29 => (P4,(P8,P13)) | L30 => (P3,(P9,P14))end.

Lemma a3_1 : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A = B /\ ~ A = C /\ ~ B = C /\ Incid A l /\ Incid B l /\ Incid C l)}}}.
Proof.
 intros l; pose (xyz := f_a3_1 l); exists (fst xyz); exists (fst (snd xyz)); exists (snd (snd xyz)).
  destruct l; solve [split; [intro; discriminate | split; [intro; discriminate | split; [intro; discriminate | split; [reflexivity | split; reflexivity]]]]].
 Qed.

Lemma a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.
Proof. exists L1; exists L2; intro;discriminate. Qed.

Module pg25 : ProjectivePlane.

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

End pg25.

