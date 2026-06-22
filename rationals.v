From mathcomp Require Import all_ssreflect all_algebra.

Open Scope ring_scope.

Definition append_last {n:nat} (v : 'rV[rat]_n) (x : rat) : 'rV[rat]_(n.+1) :=
  castmx (erefl 1, addn1 n) (row_mx v (\row_(i < 1) x)).

Definition z_x_t {m:nat} (z:'rV[rat]_m) (x:rat) (t:rat) : 'rV_(m.+2) :=
  append_last (append_last z x) t.

Section technical.

Variables n m :nat.
Variables Hn : n<>0.
Variables Hm : m<>0.
Variable M:'M[rat]_(m.+1,m.+2).

Lemma technical_lemma : 

(forall z:'rV[rat]_(m.+2), 

forall y:'rV[rat]_(m.+1),
(z = y*m M) -> \sum_(i<m) (z 0 (inord i) )*(z 0  (inord i)) + n%:R*(z 0 (inord m))*(z 0 (inord m)) = \sum_(i<m.+1) (y 0 i )*(y 0  i ) + (z 0 (inord (m.+1)))*(z 0 (inord (m.+1)))) -> 

exists y:'rV[rat]_(m.+1), 
  
     forall z:'rV[rat]_(m.+2), z = y*m M -> 
       n%:R*(z 0 (inord m))*(z 0 (inord m)) = (y 0 (inord m))*(y 0 (inord m) + (z 0 (inord (m.+1)))*(z 0 (inord (m.+1)))) /\ (z 0 (inord m))<>0.
Proof.
Admitted.

Lemma technical_lemma2 : 

(forall x:rat, forall t:rat, 
 forall z:'rV[rat]_(m), 

forall y:'rV[rat]_(m.+1),
(z_x_t z x t = y*m M) -> \sum_(i<m) (z 0 i )*(z 0  i ) + n%:R*x*x = \sum_(i<m.+1) (y 0 i )*(y 0  i ) + t*t) -> 

exists y:'rV[rat]_(m.+1), 
  forall x:rat, forall t:rat, 
     forall z:'rV[rat]_(m), z_x_t z x t = y*m M -> 
       n%:R*x*x = (y 0 (inord m))*(y 0 (inord m) + t*t) /\ x<>0. 
Proof.
Admitted.

End technical.
