(*open Stdlib*)
(*open Format*)
(*open Char*)
open String
(*open Unix*)

let prelude = "Require Import PG2X.projective_plane_axioms.\n\n"

let rec max cand l =
  match l with
     [] -> cand
   | x::xs -> if (x>cand) then max x xs else max cand xs
      
let rec print_list = function 
    [] -> ()
  | e::l -> print_int e ; print_string " " ; print_list l

let rec string_list = function 
    [] -> ""
  | e::l -> cat (cat "| P" (string_of_int e)) (cat " " (string_list l))
  
let rec read_file f acc =
  try
    let l = trim (input_line f) in read_file f (acc@[l])
  with End_of_file -> acc;;

let split_line l =
  List.map int_of_string (split_on_char ' ' l);;

let rec upto n =
  if (n=0) then [0] else (upto (n-1))@[n]

let points n =
  cat "Inductive Point : Set :=" 
    (cat (List.fold_right (fun x y -> (cat (cat " | P" (string_of_int x))y)) (upto n) "") ".\n\n");;

let lines n =
  cat "Inductive Line : Set :=" 
    (cat (List.fold_right (fun x y -> (cat (cat " | L" (string_of_int x))y)) (upto n) "") ".\n\n");;

let incidence ll =
  let size = List.length ll in 
  let up = upto (size-1) in 
  "Definition incid x l := match l with\n" ^ 
    (List.fold_right (fun x y ->  " | L" ^ (string_of_int x) ^ " => match x with " ^
                                              (string_list (List.nth ll x)) ^ " => true | _ => false end \n" ^ y) up "") ^
  "end.\n\nDefinition Incid x l := incid x l = true.\n\n"

(*
    cat (List.fold_right (fun x y -> (cat (cat " | P" (string_of_int x)) y)) [1;2;3] "")  " => true | _ => false end ";;   
 *)

let strip =
  function None -> failwith "strip"
 | Some x -> x

let l_from_points ll =
  let up = upto ((List.length ll)-1) in
  let l_from_points x y = string_of_int (strip (List.find_index ((fun l -> (List.mem x l && List.mem y l))) ll)) in 
  "Definition l_from_points (x y:Point) := match x with\n" ^
    (List.fold_right (fun x y ->  " | P" ^ (string_of_int x) ^ " => match y with" ^ (List.fold_right (fun x' y' ->  " | P" ^ (string_of_int x') ^ " => L"^ (l_from_points x x') ^ y') up "") ^ " end \n" ^ y) up "") ^
      "end.\n\n"

let rec inter l1 l2 = match l1 with 
    [] -> []
  | e::l -> if (List.mem e l2) then [e] else inter l l2

let p_from_lines ll =
  let up = upto ((List.length ll)-1) in
  let p_from_lines x y = string_of_int (List.hd (inter (List.nth ll x) (List.nth ll y))) in 
  "Definition p_from_lines (x y:Line) := match x with\n" ^
    (List.fold_right (fun x y ->  " | L" ^ (string_of_int x) ^ " => match y with" ^ (List.fold_right (fun x' y' ->  " | L" ^ (string_of_int x') ^ " => P"^ (p_from_lines x x') ^ y') up "") ^ " end \n" ^ y) up "") ^
    "end.\n\n"

let uniqueness =
"Lemma foo : forall P:Prop, false=true -> P.
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
Proof. intros; destruct A; destruct B; solve [left; reflexivity | right; intro; discriminate]. Qed.\n\n"


let lemma_a1 = "Lemma a1_exist : forall (A B : Point) , {l : Line | Incid A l /\\ Incid B l}.\nProof. intros A B; exists (l_from_points A B); destruct A; destruct B; exact_no_check (conj (@eq_refl bool true)(@eq_refl bool true)). Qed.\n\n"

let lemma_a2 = "Lemma a2_exist : forall (l1 l2 : Line), {A : Point | Incid A l1 /\\ Incid A l2}.\nProof. intros l1 l2; exists (p_from_lines l1 l2); destruct l1; destruct l2; exact_no_check (conj (@eq_refl bool true)(@eq_refl bool true)). Qed.\n\n"

let lemma_uniqueness = "Lemma uniqueness : forall (A B : Point)(l1 l2 : Line),
  Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A = B \\/ l1 = l2.\nProof. intros; destruct (eq_Point_dec A B) ; [left; assumption | right; intros; handle l1; handle l2; reflexivity]. Qed.\n\n"

let to_string_first_three = 
  function
    x::y::z::t -> "(P"^(string_of_int x)^",(P"^(string_of_int y)^",P"^(string_of_int z)^"))"
  | _ -> failwith "list too short"

let rec to_string = function
    [] -> ""
  | x::xs -> ("(P"^(string_of_int x)^(if xs<>[] then "," else "")^(to_string xs)^")")
    
    
let f_a3_1 ll =
  let up = upto ((List.length ll)-1) in
  "Definition f_a3_1 (l:Line) := match l with" ^ ((List.fold_right (fun x y ->  " | L" ^ (string_of_int x) ^ " => "^ (to_string_first_three (List.nth ll x)) ^ y) up ""))^"end.\n\n"

let lemma_a3_1 = "Lemma a3_1 : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A = B /\\ ~ A = C /\\ ~ B = C /\\ Incid A l /\\ Incid B l /\\ Incid C l)}}}.\nProof.\n intros l; pose (xyz := f_a3_1 l); exists (fst xyz); exists (fst (snd xyz)); exists (snd (snd xyz)).
  destruct l; solve [split; [intro; discriminate | split; [intro; discriminate | split; [intro; discriminate | split; [reflexivity | split; reflexivity]]]]].\n Qed.\n\n"

let lemma_a3_2 = "Lemma a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.\nProof. exists L1; exists L2; intro;discriminate. Qed.\n\n"

let instance xx = "Module "^xx^" : ProjectivePlane.\n
  Definition Point := Point.
  Definition Line := Line.\n
  Definition Incid := Incid.\n
  Lemma a1_exist : forall (A B : Point) , {l : Line | Incid A l /\\ Incid B l}.
  Proof. exact a1_exist. Qed.\n
  Lemma a2_exist : forall (l1 l2 : Line), {A : Point | Incid A l1 /\\ Incid A l2}.
  Proof. exact a2_exist. Qed.\n
  Lemma uniqueness : forall (A B : Point)(l1 l2 : Line),
      Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A = B \\/ l1 = l2.
  Proof. exact uniqueness. Qed.\n
  Lemma a3_1 : forall l : Line,
      {A : Point & {B : Point & {C : Point |
           (~ A = B /\\ ~ A = C /\\ ~ B = C /\\ Incid A l /\\ Incid B l /\\ Incid C l)}}}.
  Proof. exact a3_1. Qed.\n
  Lemma a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.
  Proof. exact a3_2. Qed.\n
End "^xx^".\n\n"
          
let rec fix_nb_points ll order =
  match ll with
    [] -> []
  | x::[] -> if ((List.length x)<>(order+1)) then failwith "fix_nb_points: last line is not ok." else [x]
  | x::y::xs -> if ((List.length x)<(order+1)) then (List.append x y)::(fix_nb_points xs order) else x::(fix_nb_points (y::xs) order)
    

let main () =
  let _ = print_string "Generating specifications for projective planes PG(2,q) (c) Nicolas Magaud\n" in 
  let nb_args = Array.length Sys.argv - 1 in 
  let _ = if (nb_args<1) then
            let _ = print_string (cat "usage: " (cat Sys.argv.(0) " <input.txt> [ -o <output.v> ]\n")) in exit(1) in 
  let _ = for i = 0 to nb_args do
            Printf.printf "[%i] %s " i Sys.argv.(i) done in
  let _ = Format.print_string "\n" in
  let _ = Format.print_flush () in 
  let output_filename = if ((nb_args>2)&&(Sys.argv.(2)="-o")) then Sys.argv.(3) else "output.v" in 
  let filename = Sys.argv.(1) in
  let whichpg = try List.hd (split_on_char '.' filename) with _ -> failwith "whichpg:filename does not contain '.'." in
  let order = try
      let v = List.hd (split_on_char '.' filename) in int_of_string (String.sub v 3 ((String.length v)-3)) with _ -> failwith "order:filename does not contain '.'." in
  (*  let _ = print_int order in *)
  let file = open_in filename in
  let ll = fix_nb_points (List.map split_line (read_file file [])) order in
  
  (*  let _ = print_list (List.hd (List.tl ll)) in*)

  let output = open_out output_filename  in 
  let _ = output_string output prelude in 
  let nb_points = max (-1) (List.flatten ll) in
  let _ = output_string output (points nb_points) in
  let _ = Format.print_flush () in 
  let _ = output_string output (lines nb_points) in
  let _ = Format.print_flush () in
  let _ = output_string output (incidence ll) in


  let _ = output_string output (l_from_points ll) in
  let _ = output_string output lemma_a1 in
  let _ = output_string output (p_from_lines ll) in
  let _ = output_string output lemma_a2 in
  let _ = output_string output uniqueness in
  let _ = output_string output lemma_uniqueness in
  let _ = output_string output (f_a3_1 ll) in
  let _ = output_string output lemma_a3_1 in
  let _ = output_string output lemma_a3_2 in
  let _ = output_string output (instance whichpg) in
  
  let _ = close_out output in 
  Format.print_flush ();;

main ()
