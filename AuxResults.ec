
require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.


(* Chinese Reminder Theorem  *)
op LCM (M : int -> int) (size : int) : int.

axiom nosmt LCM_pos M n :  0 <= LCM M n.

axiom nosmt chinese_reminder_theorem x M size : 
   (forall i, 0 <= i < size => x %% M i = 0)
    <=>
    x %% LCM M size = 0.


lemma nosmt mul_weaken6 (b a c : int) : 0 < b => a * b <= c * b => a <= c.
smt().
qed.    
    
lemma nosmt wekenq a q : a = 0 => a %% q = 0.
move => h. rewrite h.
smt(@Int).
qed.

lemma nosmt add_weaken1 (a b c d : int) : a <= c => b <= d => a + b <= c + d.
smt().
qed.    


lemma nosmt mul_weaken4 (a b c : int) : 0 < b => a < c => a * b < c * b.
smt().
qed.    


lemma nosmt sub_weaken3 (a b c : int) : b <= 0 => c <= b => a - b <= a - c.
smt().
qed.    


lemma nosmt sub_weaken2 (a b : int) : b <= 0 => a <= a - b.
smt().
qed.    


lemma nosmt mulnegpos (a b : int) : a <= 0 => 0 <= b => a * b <= 0.
smt().
qed.    

lemma leq_sub_weak (a b c : int) : a <= b => c <= 0 => a <= b - c.
smt().
qed.    

lemma nosmt mul_leq (a b c : int) : 0 <= b =>  a <= c => a * b <= c * b.
smt().
qed.    


lemma nosmt add_weaken (a b c : int) : 0 <= b => a + b < c => a < c.
smt().
qed.    


lemma nosmt sub_weaken (b a c : int) : 0 <= b => a < c => a - b < c.
smt().
qed.    


lemma nosmt mul_pos (a b : int) : 0 <= a => 0 <= b => 0 <= a * b .
smt().
qed.    

lemma nosmt hjhjj (a b c d e : int) :
     a - b - c <= d - b - e <=> a - c <= d - e.
smt().
qed.

lemma nosmt hhelp (a b k x : int) :
     x - (a + b) * k = x - a * k - b * k.
smt().
qed.    


lemma nosmt ltr_weaken (c a b : int) : 0 <= c => a <= b => a - c <= b.
smt().
qed.    


lemma nosmt lhsub1 (a b : int) : a <= b <=> -b <= -a.
smt().
qed.    


lemma nosmt lhsub2 (a b : int) : - (a - b) = (b - a).
smt().
qed.    


lemma nosmt passoc (a b c : int) : a + (b + c) =  a + b + c.
smt().
qed.    


lemma nosmt ltr_weaken2 (a b c d : int) :
      a <= c
   => b <= d
   => a + b <= c + d.
smt().
qed.   


lemma nosmt ltr_turnaround (a b : int) : a < b <=> - b < - a.
smt().
qed.    

lemma nosmt ltr_plusc (a b c : int) : a + c <= b + c <=> a <= b.
smt().
qed.    


lemma nosmt ltr_plusc2 (a b c : int) : c + a <= c + b <=> a <= b.
smt().
qed.  

lemma nosmt neg_neg (a  : int) : - - a = a.
smt().
qed.    

lemma nosmt min_out_in (a b c : int) : - (a - b - c) = (b + c) - a.
smt().
qed.    

lemma nosmt hjhj (a b c : int) : a < c => 0 <= b < c => 0 <= c => a - b < c.   
smt(@Int).
qed.
    

lemma nosmt qqqqq a b c :  0 <= a < c => 0 <= b < c => -c < a - b < c.
    smt(@Int).
qed.

lemma nosmt jkjk (a b c : int) : (a - b - c) = (a - c - b).
    smt().
    qed.


lemma nosmt kk (x y m : int) : 0 <= m => x <= y => x * m <= y * m.
smt(@Int).
qed.    

lemma nosmt qq (x y l m : int) : 
  0 <= x => 
  0 <= y =>  
  x <= l => 
  y <= m =>  
  (x * y) <= (l * m).
smt (ler_pmul).
qed.    


lemma nosmt bb (a b c x y : int)  : 
     0 <= a < c 
  => 0 <= b < c  
  => 0 <= x < a 
  => 0 <= y < b
  => -c < x - y < c.
proof.     smt (@Int).
qed.


lemma nosmt min_min_plus (a b c : int)  :  
  a - b - c = a - (b + c).
proof. smt(@Int). qed.


lemma nosmt eq_mod (a b q : int)  :  
  a = b => a %% q = b %% q.
proof. smt(). qed.

lemma nosmt qqq x m :  0 <= x < m => x %% m = 0 => x = 0.
smt(@Int).
qed.

lemma nosmt ooo (x m : int) :   - m < x <= 0 => x %% m = 0 => x = 0.
  smt(modzE @Int).
qed.


lemma nosmt grand (x m : int) :  - m < x < m => x %% m = 0 => x = 0.
smt (qqq ooo).
qed.


lemma nosmt jjjj (c a b : int) :  a <= b => a - c <= b - c.
smt().
qed.


lemma nosmt muldiv (k q : int) : 0 < q => k = (k * q) %/ q.
    smt(@Int).
qed.    

lemma eqmodP0:
 forall (m a : int), a %% m = 0 <=> exists (c : int), a = c * m.
admitted.

    
lemma nosmt bounds x (k: int) q a b :
  0 < q =>
  x = k * q => 
  a <= x <= b => 
  a  %/ q <= k <= b %/ q.
progress.
have -> : k = (k * q) %/ q. apply muldiv => //.
apply leq_div2r => /#.
have -> : k = (k * q) %/ q. apply muldiv => //.
apply leq_div2r => /#.
qed.


lemma nosmt bounds2 (q a b : int) :
  0 < q =>
  a <= b => 
  a  %/ q <= b %/ q.
smt().
qed.    

lemma nosmt big_mod m F  : forall nlimbs, (bigi predT F 0 nlimbs) %% m 
  = (bigi predT  (fun x => (F x) %% m) 0 nlimbs) %% m.
apply natind. 
progress. congr. congr.
rewrite big_geq. auto.
rewrite big_geq. auto. auto.
progress.
rewrite big_int_recr_cond. auto.
rewrite big_int_recr_cond. auto.
rewrite /predT. simplify.  
rewrite - modzDm.
rewrite H0. simplify. rewrite /predT.
rewrite  modzDm.
rewrite - modzDmr.  
auto.
qed.  
  

lemma compl1 (a q : int) : 0 < q => q %| a => a %/ q * q = a.
smt(@Int).    
qed.


lemma compl2 (a b : int) : - a <= b => 0 <= b + a .
smt(@Int).    
qed.

lemma compl3 (a b q : int) : 0 < q =>  a <= b => ((a %/ q) * q) <= b.
smt(@Int).    
qed.


lemma compl4 (a b q : int) : 0 < q =>  - a <=  - ((a %/ q) * q) .
smt(@Int).    
qed.


lemma divz_eqP (m d n : int) :
  0 < d => m %/ d = n <=> n * d <= m < (n + 1) * d.
proof. smt(@IntDiv).
qed.



require import IntDiv.
lemma floor_div1 a b : 0 < b => a %/ b = floor (a%r / b%r).
move => qp.
apply (divz_eqP     a b (floor (a%r / b%r)) qp).
progress. 
have h1 : (floor (a%r / b%r))%r <= a%r / b%r.
smt (floor_bound).
progress. 
have h2 : (a%r / b%r) * b%r <= a%r. smt().
have z : (floor (a%r / b%r))%r <= a%r  / b%r.     smt.
have : (floor (a%r / b%r))%r * b%r <= a%r. 
    smt.
smt.    
have h1 : a%r < (floor (a%r / b%r) + 1)%r * b%r.
smt (floor_bound).
progress. 
have h2 : a%r < ((a%r / b%r) + 1%r) * b%r. smt().
smt().
qed.



lemma miguels (a x q : int) : 0 < q => q %| x => - a <= x  => - a %/ q * q <= x.
progress.
have : exists k, x = k * q.
apply eqmodP0.   apply  H0. elim. move => k.
move => h.
rewrite h.
   have p1 : (-a)%r <= x%r. smt(@Real).
   have p2 : (-a)%r / q%r <= x%r / q%r. smt(@Real).
   have p3 : ceil ((-a)%r / q%r) <= ceil (x%r / q%r). smt(@Real).
   have p4 : ceil ((-a)%r / q%r) <= ceil (k%r). smt(@Real).
   have p5 : ceil ((-a)%r / q%r) <= k. smt(@Real).
   have p6 : - floor (a%r / q%r) <= k. smt(@Real).
   have p7 : - a %/ q <= k. rewrite floor_div1. auto. auto.
   have p8 : (- a %/ q) * q <= k * q. smt().
   have p9 : (- a %/ q) * q = - (a %/ q * q).
   smt.  
smt().
qed.




 
    (* search (<=) (%|). *)
(* lemma miguels_lemma (a b q : int) :  0 < a => 0 < b => 0 < q => q %| b => a %/ q <= b %/ q => a <= b. *)
(* proof. timeout 20. smt.     *)
(* qed. *)

lemma nosmt ltemul (a b q : int)  :  0 < q => 
  a * q <= b * q  => a <= b.
proof. progress. smt().
qed.

lemma nosmt muldivaux (a k q : int)  :  0 < q =>
  a  = k * q  => k = a %/ q.
proof.   smt (eqz_div @Int). qed.


lemma nosmt min_eq (a b : int)  :  
  a - b = 0 <=> a = b.
proof. smt(@Int). qed.


lemma nosmt modzBml:
  forall (m n d : int), (m %% d - n %% d) %% d = (m %% d - n) %% d.
progress.
    rewrite modzBm.
rewrite - modzBm.
rewrite - (modzBm (m %% d) n d).
rewrite modz_mod. auto.
qed.


lemma nosmt modzBmr2:
  forall (m n d : int), (m - n %% d) %% d = (m - n ) %% d.
progress.
rewrite - modzDml.
rewrite modzBm. auto.
qed.    

    
lemma nosmt modzBmr:
  forall (m n d : int), (m %% d - n %% d) %% d = (m - n %% d) %% d.
progress.
rewrite  modzBm.
rewrite modzBmr2.
rewrite - modzDm. auto.
qed.


lemma nosmt min_min a b c m : (a %% m - b %% m - c %% m) %% m = (a - b - c %% m) %% m.
rewrite modzBmr2.
rewrite modzBmr2.        
rewrite - modzDm.
rewrite modzBm.            
rewrite modzDm.
auto.
qed.    


lemma nosmt min_min2 (a b c m : int) : (a - b - c) %% m = (a %% m - b %% m - c %% m) %% m.
rewrite -     modzBmr2.
smt( min_min).
qed.    



lemma nosmt popop (a b : int) : - (a - b) = b - a.
smt().
qed.


lemma nosmt popop2 (a b c : int) : a + (b - c) = (a + b) - c.
smt().
qed.


lemma nosmt popop3 (a b c d : int) : a <= c => b <= d => a + b <= c + d.
smt().
qed.


lemma nosmt popop4 (a b c : int) : a + b - c = a + (b - c).
smt().
qed.


lemma nosmt popop5 (c a b : int) : a <= c => a - b <= c - b.
smt().
qed.

