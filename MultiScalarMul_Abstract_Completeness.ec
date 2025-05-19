require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.


require import MultiScalarMul_Abstract.
require import Distr.

  (* add group order premise n < p *)
axiom funny_one n b :  exists (x : R), n *** x = b.
axiom r_distr_full : is_full r_distr.
axiom r_distr_uni : is_uniform r_distr.
(* only if gcd(n,order) = 1 *)
axiom const_mul_inj : forall n, 1 <= n => forall x y, n *** x = n *** y => x = y.


op u_check (r : R) : bool.
op table_check (P : int -> R) (r : R) : bool.

op p1 : real.
axiom p1_prop x : mu r_distr (fun r => x = xof r) <= p1.

op p2 : real = mu r_distr (fun (x : R) => ! u_check x).

op p3 (P : ( int -> R)) :  real 
   = mu r_distr (fun (x : R) => ! table_check P x).



lemma mu_split distr P Q :
    mu distr (fun (x : 'a) => ! (P x /\ Q x)) = 
     mu distr (fun (x : 'a) =>  (!P x \/ !Q x)).
smt(). qed.    


lemma mu_or_leq distr P Q :
     mu distr (fun (x : 'a) =>  (P x \/ Q x))
     <= mu distr P   
       + mu distr Q.
rewrite Distr.mu_or.
smt(@Distr).
qed.    

require import Real.

lemma mu_or_leq_param distr p q P Q:  
     mu distr P <= p
     => mu distr Q <= q
     => mu distr (fun (x : 'a) =>  (P x \/ Q x)) <= p + q.
progress.
have z : mu distr (fun (x : 'a) => P x \/ Q x)
    <=  mu distr P   
       + mu distr Q.
apply mu_or_leq.
apply (RealOrder.ler_trans (mu distr P + mu distr Q)).      
apply z.
smt().
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



lemma r_distr_funi : is_funiform r_distr.
proof. apply is_full_funiform.
apply r_distr_full.
apply r_distr_uni.
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


op predicate (x : R) (r : R) = xof x <> xof r.



op helperI_pure (l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argic : int) (argcc : R) 
    = (iteri l (fun j (acc : bool * R) 
        => (acc.`1 /\ predicate acc.`2 (argT j (args j argic)) , acc.`2 %%% argT j (args j argic))) (true, argcc)).

  
op multiScalarMulII_pure (T l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argu : R) (argw : int)
    = (iteri T (fun i (acc : bool * R) 
        => let r = helperI_pure l argT args i ((2 ^ argw) *** acc.`2) in (acc.`1 /\ r.`1, r.`2)) (true, argu)).



module type UCompute = {
  proc run() : R
}.


module type TCompute = {
  proc run(P : int -> R, u_cand : R) : (bool * (int -> int -> R))
}.

op point_distr : Point distr.

module UniformU : UCompute = {
   proc run() = {
     var u_cand;
     u_cand <$ r_distr;
     return u_cand;
   }
}.

module PerfectTable : TCompute = {
   proc run(P : int -> R, u_cand : R)  = {
     var flag, table;
     flag   <- table_check P u_cand;
     table  <- perfect_table_pure P ((2 ^ w - 1) *** u_cand);
     return (flag, table);
   }
}.

module SimpleComp = {
  proc multiScalarMul_Iter11(p : R, w : int) = {
      var cnt;
      cnt <- 0;
      while (cnt < w) {
        p <- p +++ p;
        cnt <- cnt + 1;
      }
      return p;
  }


  proc multiScalarMul_Iter12(acc : R, table : int -> int-> R, ic : int, s : int -> int -> int) =    {
      var jc, aux, vahe, flag;
    
      aux <- witness;
      flag <- true;
      jc <- 0;
      vahe <- acc;
      while (jc < l) {
        aux <- table jc (s jc ic);
        flag <- flag /\ predicate vahe aux;
        vahe <- (vahe %%% aux);

        jc <- jc + 1;
      }
      return (flag, vahe);
  }



  proc multiScalarMul_Iter1(P : int -> R, s : int -> int -> int, U : R, table : int -> int -> R ) = {
    var acc, aux, result : R;

    var ic, jc, cnt : int;
    var flag, flagaux : bool;

    flag    <- true;
    flagaux <- true;
    acc     <- l *** U;
    ic      <- 0;
    while (ic < T) {
      acc <@ multiScalarMul_Iter11(acc,w);

      (flagaux, acc) <@ multiScalarMul_Iter12(acc, table, ic, s);
      flag <- flag && flagaux;
      ic <- ic + 1;
    }    
    return (flag, acc);
  }

  proc multiScalarMul_Fun(P : int -> R, s : int -> int -> int) = {
    var u_cand, flag, result, table;

    u_cand <$ r_distr;

   (* check u *)
   flag   <- u_check u_cand;

   (* check table  *)
   flag   <- flag /\ table_check P (u_cand);
   table  <- perfect_table_pure  P ((2 ^ w - 1) *** ( u_cand));

   (* do the double-and-add computation  *)
   result <- multiScalarMulII_pure T l table s (l *** ( u_cand)) w;

   return (flag /\ result.`1, result.`2 +++ (- (l *** ( u_cand))));
  }


}.

module NestedLoops(T : TCompute, U : UCompute) = {

  proc multiScalarMul(P : int -> R, s : int -> int -> int) = {
    var u_cand : R;
    var flag, flagaux : bool;
    var result, table;

    (* choose a point (uniformly for completeness, adversarially for soundness *)
    u_cand <@ U.run(); 
    (* perform the checks on U  *)
    flag   <- u_check u_cand;

    (* try to compute the Table or fail  *)
    (flagaux, table) <@ T.run(P, u_cand);
    flag <- flagaux /\ flag;
  
    (* double and add loops  *)
    result <@ SimpleComp.multiScalarMul_Iter1(P, s, u_cand, table);

    return (flag /\ result.`1, result.`2 +++ (- (l *** u_cand)));
  }
 

}.


lemma multiScalarMul_Iter12_specR_ph argcc argT argic args  :
 phoare [ SimpleComp.multiScalarMul_Iter12 : arg = (argcc, argT, argic,  args)
     ==>  res = helperI_pure l argT args argic argcc ] = 1%r.
proc.
while (0 <= jc 
 /\ jc <= l 
 /\ flag = (iteri 
                  jc 
                  (fun j (acc : bool * R) => 
                     (acc.`1 /\ predicate acc.`2 (argT j (args j argic)) , 
                      acc.`2 %%% argT j (args j argic))) 
                  (true, argcc)).`1
 /\ (acc, table, ic,  s) = (argcc, argT, argic, args) 
 /\ vahe =  (iteri jc (fun j (acc : bool * R) => (acc.`1 /\ predicate acc.`2 (argT j (args j argic)) , acc.`2 %%% argT j (args j argic))) (true, argcc)).`2) (l - jc).
move => z.
wp. skip. progress. smt(). smt(). rewrite iteriS. smt().
   simplify.
   rewrite /predicate. 
pose xxx := (iteri jc{hr}
     (fun (j : int) (acc0 : bool * R) =>
        (acc0.`1 /\
         xof acc0.`2 <> xof (table{hr} j (s{hr} j ic{hr})) && acc0.`2 <> idR,
         acc0.`2 %%% table{hr} j (s{hr} j ic{hr}))) (true, acc{hr})).
pose yyy := (iteri jc{hr}
       (fun (j : int) (acc0 : R) => acc0 %%% table{hr} j (s{hr} j ic{hr}))
       acc{hr}).     smt().
rewrite iteriS. smt().
smt(op_assoc).
smt().   
   wp. skip. progress. smt(l_pos). 
rewrite iteri0. auto. auto.
rewrite iteri0. auto. auto.
smt().   
smt().
qed.  


lemma multiScalarMul_Iter12_specR_h argcc argT argic args  :
 hoare [ SimpleComp.multiScalarMul_Iter12 : arg = (argcc, argT, argic,  args)
     ==>  res = helperI_pure l argT args argic argcc ].
conseq (multiScalarMul_Iter12_specR_ph argcc argT argic args).
qed.   


lemma doublewtimes_spec_ph argP argw :
 phoare [ SimpleComp.multiScalarMul_Iter11 : arg = (argP, argw) /\
   0 <= argw  ==>  res = (2 ^ argw) *** argP  ] = 1%r.
proc. 
   while (cnt <= w /\ 0 <= argw /\ 0 <= cnt /\ p = (2 ^ cnt) *** argP) (w - cnt).
move => z.    
   wp.
   skip. progress. smt(). smt().
   rewrite qiq. smt.
   have ->: (2 ^ cnt{hr} + 2 ^ cnt{hr}) = (2 * 2 ^ cnt{hr} ).
   smt(@Int).
   congr.
   rewrite exprS. auto. auto.
   smt().
   wp. skip. progress. smt. smt().
   smt(@Int).
qed.


lemma doublewtimes_spec argP argw :
 hoare [ SimpleComp.multiScalarMul_Iter11 : arg = (argP, argw) /\
   0 <= argw  ==>  res = (2 ^ argw) *** argP  ].
conseq (doublewtimes_spec_ph argP argw).   
qed.   


lemma multm_spec_h argP args argU argtable :
 hoare [ SimpleComp.multiScalarMul_Iter1 : arg = (argP, args, argU, argtable)   
  ==>  res = multiScalarMulII_pure T l argtable args (l *** argU) w   ] .
proc. 
while (
  0 <= ic 
  /\ ic <= T
  /\ (U, table, s) = (argU, argtable, args) 
  /\ (flag , acc) = multiScalarMulII_pure ic l argtable args (l *** argU) w
 ) .
wp.
ecall (multiScalarMul_Iter12_specR_h acc argtable ic args).
ecall (doublewtimes_spec acc w). 
skip.
progress. smt(w_pos).
smt(). smt().
rewrite /multiScalarMulII_pure.
rewrite iteriS. smt().
smt().
wp. skip. progress. smt(T_pos).   
rewrite /multiScalarMulII_pure. rewrite iteri0.
auto. auto. 
have -> : T = ic0. smt(T_pos).
rewrite - H2.
 smt().
qed. 

lemma multm_spec_ph argP args argU argtable :
 phoare [ SimpleComp.multiScalarMul_Iter1 : arg = (argP, args, argU, argtable)   
  ==>  res = multiScalarMulII_pure T l argtable args (l *** argU) w ]  = 1%r.
phoare split ! 1%r 0%r. auto.
   proc. wp.
while (table = argtable /\ s = args) (T - ic). progress.
wp.
exists* acc, table, ic, s.
elim*. move => accV tableV icV sV.
call (multiScalarMul_Iter12_specR_ph (2 ^ w *** accV) argtable icV args).
call (doublewtimes_spec_ph accV MultiScalarMul_Abstract.w).
skip.  progress. smt(w_pos).  smt().
wp. progress.
auto. smt(). hoare.
apply multm_spec_h. 
qed.


section.

declare module T <: TCompute.

declare axiom T_prop Parg uarg : phoare  [ T.run : arg = (Parg, uarg) ==> (res.`1 => res.`2 = perfect_table_pure Parg ((2 ^ w - 1) *** uarg)) /\ res.`1 = table_check Parg uarg ] = 1%r.


lemma compl_I_equiv : 
 equiv [ SimpleComp.multiScalarMul_Fun ~
         NestedLoops(T, UniformU).multiScalarMul
     : ={arg} ==> res{1}.`1 = res{2}.`1 ].
proc.
seq 4 4 : (#pre /\ ={u_cand} /\ (flag{1} => ={table}) /\ ={flag}). 
inline UniformU.run. wp.
ecall {2} (T_prop P{2} ((u_cand{2}))).
wp. 
   
rnd. skip. progress. smt(). smt().
exists* P{2}, s{2}, u_cand{2}, table{2}. elim*. move => PV sV u_candV tableV.  
wp. 
call {2} (multm_spec_ph PV sV (u_candV) tableV).
wp. skip. progress. smt().
qed.

end section.


lemma compl_I_equiv_perf : 
 equiv [ SimpleComp.multiScalarMul_Fun ~
         NestedLoops(PerfectTable, UniformU).multiScalarMul
     : ={arg} ==> ={res} ].
proc.
seq 4 4 : (#pre /\ ={flag, u_cand, table}). 
inline PerfectTable.run UniformU.run.
wp. rnd. skip. progress. smt().
exists* P{2}, s{2}, u_cand{2}, table{2}. elim*. move => PV sV u_candV tableV.  
call {2} (multm_spec_ph PV sV (u_candV) tableV).
wp. skip. progress.
qed.





lemma mu_split_q distr P Q p :
     mu distr P + mu distr Q <= p =>
     mu distr (fun (x : 'a) =>  (P x \/ Q x)) <= p.
apply RealOrder.ler_trans. apply mu_or_leq.
qed.    


lemma kkkk (a b c d : real) : a <= c => b <= d => a + b <= c + d.
smt().
qed.    


require import Distr.


lemma completeness_I argP args :
  phoare [ SimpleComp.multiScalarMul_Fun :
      arg = (argP , args) ==> !res.`1 ] 
            <= (p2 + (p3 argP) + (T%r * (l%r * p1))).
proc.
wp. rnd. skip. progress. 
rewrite /multiScalarMulII_pure.
pose f := fun a i b => 
  (helperI_pure l (perfect_table_pure P{hr} ((2 ^ w - 1) *** a))
    s{hr} i (2 ^ w *** b)).
simplify.
rewrite mu_split. simplify.
apply mu_split_q.
rewrite mu_split. simplify.
apply kkkk.
apply mu_split_q.  
apply kkkk. auto.
auto.


apply (iteri_ub (fun (x : R) => l *** x) f  r_distr (l%r * p1) _ T _)  .  
move => i acc.
rewrite /f. rewrite /helperI_pure.   
pose h := fun  a j b
    =>  ((predicate b
               (perfect_table_pure P{hr} ((2 ^ w - 1) *** a) j (s{hr} j i)))
        , b %%% perfect_table_pure P{hr} ((2 ^ w - 1) *** a) j (s{hr} j i)).
apply  (iteri_ub (fun (x : R) => 2 ^ w *** acc) h r_distr p1).  
progress.
rewrite /h. simplify.           
rewrite /perfect_table_pure. simplify.
rewrite /predicate.            
simplify.

 have -> : (fun (r : R) =>
     xof (acc0) = xof (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** r))
     = (fun (r : F) =>
     xof (acc0 ) = r) \o (fun r =>  xof (s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** r)) . smt().
rewrite - dmapE. simplify.



rewrite - dmap_comp.

 have  ->:  ((dmap r_distr
        (fun (x : R) => s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x)))
   = r_distr.
   
    have -> : dmap r_distr (fun (x : R) => s{hr} i0 i *** P{hr} i0 +++ - (2 ^ w - 1) *** x) =
       dmap r_distr ((fun (x : R) => s{hr} i0 i *** P{hr} i0 +++ x) \o (fun x => - (2 ^ w - 1) *** x)). smt ().
rewrite - dmap_comp.

   have -> : (fun (x0 : R) => - (2 ^ w - 1) *** x0)
    = (fun (x0 : R) => - x0) \o (fun x => (2 ^ w - 1) *** x).   smt().
     rewrite - dmap_comp.

    have ->: (dmap r_distr (fun (x0 : R) => (2 ^ w - 1) *** x0))  = r_distr.

    pose  funny_op := fun (a : R) => choiceb (fun (x : R) => (2 ^ w - 1) *** x = a) witness.
      apply (dmap_bij _ _ _ funny_op).
     progress. apply r_distr_full.
     progress. apply r_distr_funi.
    progress.
    rewrite /funny_op.
    pose xxx := choiceb (fun (x : R) => (2 ^ w - 1) *** x = (2 ^ w - 1) *** a) witness.
      have : (2 ^ w - 1) *** xxx = (2 ^ w - 1) *** a.
     
    apply (choicebP (fun (x : R) => (2 ^ w - 1) *** x = (2 ^ w - 1) *** a)). exists a. auto. 
    
    progress.
    apply (const_mul_inj (2 ^ w - 1)). smt. auto.
    rewrite /funny_op.
    progress.
    apply (choicebP (fun (x : R) => (2 ^ w - 1) *** x = b)).
    simplify.
    apply (funny_one (2 ^ w - 1) b).
    have ->: (dmap r_distr (fun (x0 : R) => -x0)) = r_distr.
    apply (dmap_bij _ _ _ ((fun (x : R) => - x ))).    
    progress. apply r_distr_full.
    progress. apply r_distr_funi.
    progress. apply neg_neg_id.
    progress. apply neg_neg_id.
    apply (dmap_bij _ _ _ ((fun (x : R) => x +++ - s{hr} i0 i *** P{hr} i0 ))).
    progress. apply r_distr_full.
    progress. apply r_distr_funi.
    progress. smt (op_assoc op_comm op_id op_id' op_inv).
    progress. smt (op_assoc op_comm op_id op_id' op_inv).
rewrite  dmapE.    
apply p1_prop.
    smt(l_pos).
    smt(T_pos).
qed.           
