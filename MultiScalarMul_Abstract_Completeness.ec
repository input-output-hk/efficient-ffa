
require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.


require import MultiScalarMul_Abstract.

module NestedLoops = {



  proc doubleWtimes(p : R, w : int) = {
      var cnt;
      cnt <- 0;
      while (cnt < w) {
        p <- p +++ p;
        cnt <- cnt + 1;
      }
      return p;
  }


  proc helperI(acc : R, table : int -> int-> R, ic : int, s : int -> int -> int) =    {
      var jc, aux, vahe, flag;
    
      aux <- witness;
      flag <- true;
      jc <- 0;
      vahe <- acc;
      while (jc < l) {
        aux <- table jc (s jc ic);
        flag <- flag && (xof vahe) <> (xof aux);
        flag <- flag && (vahe <> idR);
        vahe <- (vahe %%% aux);

        jc <- jc + 1;
      }
      return (flag, vahe);
  }


  proc multiScalarMulII(P : int -> R, s : int -> int -> int, U : R, table : int -> int -> R ) = {
    var acc, aux, result : R;

    var ic, jc, cnt : int;
    var flag, flagaux : bool;

    flag    <- true;
    flagaux <- true;
    acc     <- l *** U;
    ic      <- 0;
    while (ic < T) {
      acc <@ doubleWtimes(acc,w);
      (flagaux, acc) <@ helperI(acc, table, ic, s);
      flag <- flag && flagaux;
      ic <- ic + 1;
    }    
    return (flag, acc);
  }


  proc multiScalarMul_Completeness_I(P : int -> R, s : int -> int -> int) = {
    var u_cand : R;
    var flag : bool;
    var result, table;

    u_cand <$ r_distr;
    table  <- perfect_table_pure P ((2 ^ w - 1) *** u_cand) ; 
    result <@ multiScalarMulII(P, s, u_cand, table);
    return result;
  }


  proc multiScalarMul_Completeness_I_fun(P : int -> R, s : int -> int -> int) = {
    var u_cand : R;
    var flag : bool;
    var result, table;

    u_cand <$ r_distr;
    table  <- perfect_table_pure P ((2 ^ w - 1) *** u_cand) ; 
    result <- multiScalarMulII_pure T l table s (l *** u_cand) w;
    return result;
  }

}.

op predicate (x : R) (r : R) = xof x <> xof r && x <> idR.

op helperI_pure (l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argic : int) (argcc : R) 
    = (iteri l (fun j (acc : bool * R) 
        => (acc.`1 /\ predicate acc.`2 (argT j (args j argic)) , acc.`2 %%% argT j              (args j argic))) (true, argcc)).

  
op multiScalarMulII_pure (T l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argu : R) (argw : int)
    = (iteri T (fun i (acc : bool * R) 
        => let r = helperI_pure l argT args i ((2 ^ argw) *** acc.`2) in (acc.`1 /\ r.`1, r.`2)) (true, argu)).


lemma helperI_specR_ph argcc argT argic args  :
 phoare [ NestedLoops.helperI : arg = (argcc, argT, argic,  args)
     ==>  res = helperI_pure l argT args argic argcc ] = 1%r.
proc.
while (0 <= jc 
 /\ jc <= l 
 /\ flag = (iteri jc (fun j (acc : bool * R) => (acc.`1 /\ predicate acc.`2 (argT j (args j argic)) , acc.`2 %%% argT j (args j argic))) (true, argcc)).`1
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



lemma helperI_specR_h argcc argT argic args  :
 hoare [ NestedLoops.helperI : arg = (argcc, argT, argic,  args)
     ==>  res = helperI_pure l argT args argic argcc ].
conseq (helperI_specR_ph argcc argT argic args).
qed.   

lemma doublewtimes_spec_ph argP argw :
 phoare [ NestedLoops.doubleWtimes : arg = (argP, argw) /\
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
 hoare [ NestedLoops.doubleWtimes : arg = (argP, argw) /\
   0 <= argw  ==>  res = (2 ^ argw) *** argP  ].
conseq (doublewtimes_spec_ph argP argw).   
qed.   


lemma multm_spec_h argP args argU argtable :
 hoare [ NestedLoops.multiScalarMulII : arg = (argP, args, argU, argtable)   
  ==>  res = multiScalarMulII_pure T l argtable args (l *** argU) w   ] .
proc. 
while (
  0 <= ic 
  /\ ic <= T
  /\ (U, table, s) = (argU, argtable, args) 
  /\ (flag , acc) = multiScalarMulII_pure ic l argtable args (l *** argU) w
 ) .
wp.
ecall (helperI_specR_h acc argtable ic args).
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
 phoare [ NestedLoops.multiScalarMulII : arg = (argP, args, argU, argtable)   
  ==>  res = multiScalarMulII_pure T l argtable args (l *** argU) w   ]  = 1%r.
phoare split ! 1%r 0%r. auto.
   proc. wp.
while (table = argtable /\ s = args) (T - ic). progress.
wp.
exists* acc, table, ic, s.
elim*. move => accV tableV icV sV.
call (helperI_specR_ph (2 ^ w *** accV) argtable icV args).
call (doublewtimes_spec_ph accV MultiScalarMul_Abstract.w).
skip.  progress. smt(w_pos).  smt().
wp. progress.
auto. smt(). hoare.
apply multm_spec_h. 
qed.


lemma compl_I_equiv : 
 equiv [ NestedLoops.multiScalarMul_Completeness_I_fun ~
         NestedLoops.multiScalarMul_Completeness_I 
     : ={arg} ==> ={res} ].
proc.
seq 2 2 : (#pre /\ ={u_cand, table}). wp. rnd. skip. progress.
exists* P{2}, s{2}, u_cand{2}, table{2}. elim*. move => PV sV u_candV tableV.  
call {2} (multm_spec_ph PV sV (u_candV) tableV).
wp. skip. progress.
qed.


op p : real.
print mu.
 
(* mu r_distr *)
(*  (fun (r : R) => (f r i acc).`1) <= p *)


axiom iteri_ub ['a 'b] (g : 'a -> 'b) (f : 'a -> int -> 'b -> (bool * 'b)) (a_distr : 'a distr) (N : int) (p : real)  :

  (forall i acc, mu a_distr
    (fun (r : 'a) => (f r i acc).`1) <= p)

  => 
  mu a_distr 
   (fun (x : 'a) => 
      (iteri N (fun j (acc : bool * 'b) 
        => 
   let r = f x j acc.`2 in(acc.`1 /\ r.`1, r.`2)) (true,  g x)).`1  ) <= N%r * p.



lemma completeness_I argP args :
  phoare [ NestedLoops.multiScalarMul_Completeness_I_fun :
      arg = (argP , args) ==> res.`1 ] <= (T%r * (l%r * p)).
proc.
wp. rnd. skip. progress. 
rewrite /multiScalarMulII_pure.


pose f := fun a i b => 
  (helperI_pure l (perfect_table_pure P{hr} ((2 ^ w - 1) *** a))
                s{hr} i (2 ^ w *** b)).


apply  (iteri_ub (fun (x : R) => l *** x) f  r_distr T   ).  

 move => i acc.
rewrite /f. rewrite /helperI_pure.   

pose h := fun  a j b
    =>  ((predicate b
               (perfect_table_pure P{hr} ((2 ^ w - 1) *** a) j (s{hr} j i)))
        ,   
   b %%%
            perfect_table_pure P{hr} ((2 ^ w - 1) *** a) j (s{hr} j i)  ).

apply  (iteri_ub (fun (x : R) => 2 ^ w *** acc) h  r_distr l  p).  
progress.
rewrite /h. simplify.           
rewrite /perfect_table_pure. simplify.
rewrite /predicate.            
