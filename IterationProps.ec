require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract_Setup.

lemma iteriG ['a 'c 'd] (g : 'a -> 'c) (h : 'a -> 'd) (f : int -> 'c -> 'd -> 'a) :   forall (n : int) , 0 <= n =>  forall (s : 'a), 
   (iteri n (fun (i : int) (acc : 'a) => f i (g acc) (h acc)) s)
     =  
        (iteri n (fun (i : int) (acc : 'a) => f i (g acc) (h ((iteri i (fun (i : int) (acc : 'a) => f i (g acc) (h acc)) s)))) s)
 .
apply natind.     
progress. rewrite iteri0. auto. rewrite iteri0. auto.  auto.
progress. rewrite iteriS. auto. simplify. rewrite iteriS. auto. simplify.  
rewrite H0. smt(). smt().
qed.
     
     
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


lemma iteriZZZZ (f : int -> R)  : 
  forall (n : int), 0 <= n => forall (z : R),
iteri n
   (fun (j : int) (acc : R) =>
      acc +++ (f j +++ z)) idR
 = iteri n
   (fun (j : int) (acc : R) =>
      acc +++ (f j)) idR +++ n *** z.
admitted.


(* lemma iteri_ub ['a 'b] (g : 'a -> 'b) (f : 'a -> int -> 'b -> (bool * 'b)) (a_distr : 'a distr) (p : real)  : *)
(*   (forall i acc, mu a_distr *)
(*     (fun (r : 'a) => !(f r i acc).`1) <= p) *)
(*   => forall (N : int), 1 <= N => *)
(*   mu a_distr *)
(*    (fun (x : 'a) => *)
(*       !(iteri N (fun j (acc : bool * 'b) *)
(*         => *)
(*    let r = f x j acc.`2 in (acc.`1 /\ r.`1, r.`2)) (true,  g x)).`1 ) <= N%r * p. *)
(* admitted.      *)



require import AuxResults.
lemma iteri_ub1 ['a 'b] (g : 'a -> 'b) (f : 'a -> int  -> (bool * 'b)) (a_distr : 'a distr) (p : real)  :

   forall (N : int), 0 <= N =>

  (forall i, 0 <= i < N => mu a_distr
    (fun (r : 'a) => !(f r i).`1) <= p) =>
  mu a_distr
   (fun (x : 'a) =>
      (iteri N (fun j (acc : bool * 'b)
        =>
   let r = f x j in (acc.`1 \/ !r.`1, r.`2)) (false,  g x)).`1 ) <= N%r * p.
apply natind. progress.

have ->: n = 0. smt(). simplify.
have ->: (fun (x : 'a) =>
     (iteri 0
        (fun (j : int) (acc : bool * 'b) =>
           ( acc.`1 \/ ! (f x j ).`1, (f x j ).`2)) (false, g x)).`1)
      = (fun (x : 'a) => false).
apply fun_ext. move => zz. rewrite iteri0. auto. simplify. auto.        smt(@Distr).
      progress.
have ->:
 (fun (x : 'a) =>
     (iteri (n + 1)
        (fun (j : int) (acc : bool * 'b) =>
           ( acc.`1 \/ ! (f x j ).`1, (f x j ).`2)) (false, g x)).`1)
= (fun x => ( (iteri n
      (fun (j : int) (acc : bool * 'b) =>
         (acc.`1 \/ ! (f x j ).`1, (f x j ).`2)) (false, g x)).`1 \/
 ! (f x n
      ).`1)).
apply fun_ext.
move => x.
rewrite iteriS. auto. simplify. progress.
have ->: (n + 1)%r * p = n%r * p + p. smt().

apply (mu_or_leq_param a_distr (n%r * p) p).
apply H0. auto.
progress. apply H2. smt().
apply H2. smt().
qed.



lemma funcong ['a 'b] (f : 'a -> 'b) g x  : f = g => f x = g x.
smt().
qed.

lemma iteri_ub2 ['a 'b] (g : 'a -> 'b) (f : 'a -> int  -> (bool * 'b))  :

   forall (N : int), 0 <= N =>

   (fun x =>
      !(iteri N (fun j (acc : bool * 'b)
        =>
   let r = f x j  in(acc.`1 /\ r.`1, r.`2)) (true,  g x)).`1 )

 =  (fun x => (iteri N (fun j (acc : bool * 'b)
        =>
   let r = f x j  in(acc.`1 \/ !r.`1, r.`2)) (false,  g x)).`1).

apply natind. progress.
apply fun_ext. move => x.
have ->: n = 0. smt().
rewrite iteri0. auto. simplify.
rewrite iteri0. auto. simplify.   auto.
progress.
apply fun_ext. move => x.
rewrite iteriS. auto. rewrite iteriS. auto.
simplify.
have -> : (! ((iteri n
       (fun (j : int) (acc : bool * 'b) =>
          (acc.`1 /\ (f x j ).`1, (f x j ).`2)) (true, g x)).`1 /\
    (f x n
       ).`1))
     
=  ( (!(iteri n
       (fun (j : int) (acc : bool * 'b) =>
          (acc.`1 /\ (f x j ).`1, (f x j ).`2)) (true, g x)).`1 \/
    !(f x n
       ).`1)). smt().

   have -> : (! (iteri n
      (fun (j : int) (acc : bool * 'b) =>
         (acc.`1 /\ (f x j ).`1, (f x j ).`2)) (true, g x)).`1)
     = (iteri n
    (fun (j : int) (acc : bool * 'b) =>
       (acc.`1 \/ ! (f x j ).`1, (f x j ).`2)) (false, g x)).`1.
   have Q : (fun (x : 'a) =>
       ! (iteri n
            (fun (j : int) (acc : bool * 'b) =>
               (acc.`1 /\ (f x j ).`1, (f x j ).`2)) (true, g x)).`1) =
    fun (x : 'a) =>
      (iteri n
         (fun (j : int) (acc : bool * 'b) =>
            (acc.`1 \/ ! (f x j ).`1, (f x j ).`2)) (false, g x)).`1.
        apply H0. auto.
apply (funcong _ _ x Q).
pose xxx := (iteri n
    (fun (j : int) (acc : bool * 'b) =>
       (acc.`1 \/ ! (f x j ).`1, (f x j ).`2)) (false, g x)).`1.
   
   have OO : forall n , 0 <= n => (iteri n
         (fun (j : int) (acc : bool * 'b) =>
            (acc.`1 /\ (f x j ).`1, (f x j ).`2)) (true, g x)).`2
  =
    (iteri n
         (fun (j : int) (acc : bool * 'b) =>
             (acc.`1 \/ ! (f x j ).`1, (f x j ).`2)) (false, g x)).`2.
   apply natind. progress.
          have ->: n0 = 0. smt(). rewrite iteri0. auto.
         rewrite iteri0. auto. auto.
      progress.
     rewrite iteriS. auto.
     rewrite iteriS. auto.
     progress.
   auto. 
qed.



lemma iteri_ub3 ['a 'b] (g : 'a -> 'b) (f : 'a -> int -> (bool * 'b)) (a_distr : 'a distr) (N : int) (p : real)  :
  (forall i, 0 <= i < N => mu a_distr
    (fun (r : 'a) => !(f r i ).`1) <= p)

  => 
  mu a_distr 
   (fun (x : 'a) => 
      !(iteri N (fun j (acc : bool * 'b) 
        => let r = f x j in  (acc.`1 /\ r.`1, r.`2)) (true,  g x)).`1 ) <= N%r * p.
progress.
  have -> : (fun (x : 'a) =>
     ! (iteri N
          (fun (j : int) (acc : bool * 'b) =>
             (acc.`1 /\ (f x j ).`1, (f x j ).`2)) (true, g x)).`1)
   =

   (fun x =>
      (iteri N (fun j (acc : bool * 'b)
        =>
   let r = f x j  in(acc.`1 \/ !r.`1, r.`2)) (false,  g x)).`1 ).

   apply   (iteri_ub2 g f N).  admit. simplify.
   apply (iteri_ub1 g f a_distr).  admit.
apply H.
qed.  


