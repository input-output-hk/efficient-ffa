
require import AllCore IntDiv CoreMap List Distr.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.



(* unique representation of points on the curve *)
type R.                  
       
(* identity element  *)
op idR : R. 
op ( +++ ) (a b : R) : R.
(* iteration of +++ n times (= iterop n ( +++ ) x idR.)  *)
op ( *** ) (n : int) (x : R) : R.  
(* inverse *)
op [-] (a : R) : R.
(* coincides with +++ under some conditions  *)
op ( %%% ) (a b : R) : R.

(* non-unique representation of points (not nec. on the curve) *)
type F.

op xof : R -> F.
op yof : R -> F.

axiom same_res (a b : R) :  a <> idR => b <> idR => xof a <> xof b 
  => a %%% b = a +++ b.
axiom opt_never_id (a b : R) :  a <> idR => b <> idR => xof a <> xof b 
  => a %%% b <> idR.
axiom no_order_two_elems x n : 0 < n => 2 ^ n *** x <> idR.



(* op properties  *)
axiom op_assoc (a b c : R) : (a +++ b) +++ c = a +++ (b +++ c).
axiom op_comm (a b : R) : a +++ b = b +++ a.
axiom op_id (x : R) :  x +++ idR = x.
axiom op_id' (x : R) : idR +++ x = x.
axiom op_inv (a : R) :  a +++ -a = idR. 



(* op iteration properties  *)
axiom one_mul (a : R) : 1 *** a = a.
axiom zero_mul (a : R) : 0 *** a = idR. 
axiom nplus_dist (i b : int) b0 :  (i + b) *** b0 = i *** b0 +++ b *** b0.
axiom nmul_mul (i b : int) b0 :  (i * b) *** b0 = i *** (b *** b0).
axiom neg_mul (i : int) b0 :  (- i) *** b0 = - (i *** b0).
axiom mul_idr : forall z, z *** idR = idR.
axiom mul_plus_distr   : forall (a : int), forall (b c : R),   
 a *** (b +++ c) = a *** b +++ a *** c.



lemma qiq : forall a, 0 <= a => forall (c : int), forall (b : R),
   a *** b +++ c *** b = (a + c) *** b.
apply natind. progress. smt.
progress. rewrite nplus_dist. auto.
have ->: (n + 1 + c) = ((n + c) + 1). smt().
rewrite nplus_dist. 
rewrite - H0. smt().    
smt(op_comm op_assoc).
qed.    

lemma const_add_inj : forall (x y a : R), x +++ a = y +++ a <=> x = y.
proof. progress.
have q : (x +++ a) +++ - a = (y +++ a) +++ - a.
    progress. smt (op_assoc op_comm op_id op_id' op_inv).
    progress. smt (op_assoc op_comm op_id op_id' op_inv).
qed.

lemma neg_neg_id : forall (x : R), - - x = x.
proof. progress.
rewrite - (const_add_inj (- - x) x (- x)). 
smt (op_assoc op_comm op_id op_id' op_inv).
qed.


lemma kik  (a b c d : R) :  a +++ b +++ (c +++ d) = a +++ c +++ (b +++ d). 
 by smt(op_assoc op_comm). qed.


lemma nosmt mulsc : forall (a : int), 0 <= a => forall b r,  a *** (b *** r) = (a * b) *** r.
apply intind.
    progress.
rewrite zero_mul. rewrite zero_mul. auto.
progress.
    rewrite nplus_dist. auto.
have ->: (i + 1) * b = i * b + b. smt().
rewrite H0.    
rewrite nplus_dist. smt.
qed.    
