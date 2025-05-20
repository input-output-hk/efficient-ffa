require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract_Setup.


lemma iteriZ : forall (n : int), 0 <= n =>  forall (z : int) (f : int -> R), z *** (iteri n (fun i acc => acc +++ f i) idR)
     = iteri n (fun i acc => acc +++ z *** (f i)) idR.
apply intind.     
progress. rewrite iteri0. auto. rewrite iteri0. auto. 
apply mul_idr.
progress.
rewrite iteriS. auto.
rewrite iteriS. auto.
simplify.
rewrite - H0.     
apply mul_plus_distr. 
qed.
     
lemma iteriZZ :  forall (n : int), 0 <= n => forall (z : R)  (f : int -> R),
   (iteri n (fun i acc => acc +++ f i +++ z) idR)
     = (iteri n (fun i acc => acc +++ f i) idR)
        +++ (iteri n (fun i acc => acc +++ z) idR).
apply intind. progress. rewrite iteri0. auto.
rewrite iteri0. auto. rewrite iteri0. auto. rewrite op_id. auto.
progress.
rewrite iteriS. auto.
rewrite iteriS. auto.
rewrite iteriS. auto.
simplify.
rewrite H0. simplify.
smt (op_assoc op_comm).
qed.     


lemma iteriZZZ  : forall (n : int), 0 <= n => forall (z : R),
  (iteri n (fun i acc => acc +++ z) idR)
     = n *** z.
apply intind. progress. rewrite iteri0. auto. rewrite zero_mul. auto.
progress.
rewrite iteriS. auto. simplify.
rewrite H0.
rewrite nplus_dist. smt.
qed.     


lemma iteri_ub ['a 'b] (g : 'a -> 'b) (f : 'a -> int -> 'b -> (bool * 'b)) (a_distr : 'a distr) (p : real)  :
  (forall i acc, mu a_distr
    (fun (r : 'a) => !(f r i acc).`1) <= p)
  => forall (N : int), 1 <= N =>
  mu a_distr
   (fun (x : 'a) =>
      !(iteri N (fun j (acc : bool * 'b)
        =>
   let r = f x j acc.`2 in (acc.`1 /\ r.`1, r.`2)) (true,  g x)).`1 ) <= N%r * p.
admitted.     
