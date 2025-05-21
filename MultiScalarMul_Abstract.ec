
require import AllCore IntDiv CoreMap List Distr.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract_Setup IterationProps.


(*  

   P := (beta, x, y) 
   1/ subset by "onCurve"
   2/ equiv. rel by  
 
       2.1/ non unique representation of "x" and "y"
       2.2/ all variations of identity point

*)



(* params  *)
op T : int.
op l : int.
op w : int.

(* params are positive  *)
axiom w_pos : 0 < w.
axiom l_pos : 0 < l.
axiom T_pos : 0 < T.

type Point.

op onCurve : Point -> bool.
op idF     : Point -> bool.
op embed   : Point -> R.

op perfect_table_pure  parg (varg : R) = 
 (fun (j i : int) =>  (i *** (parg j)) +++ - (2 ^ w - 1) *** varg).


op r_distr : R distr.


axiom r_distr_full : is_full r_distr.
axiom r_distr_uni : is_uniform r_distr.


lemma r_distr_funi : is_funiform r_distr.
proof. apply is_full_funiform.
apply r_distr_full.
apply r_distr_uni.
qed.


module type OutCalls = {
  proc getU() : Point
  proc getUniformU() : R
  proc getT(P : int -> R, v : R) : int -> int -> R
  proc getPT(P : int -> R, v : R) : bool * (int -> int -> R)
}.


op predicate (x : R) (r : R) = xof x <> xof r.
(* check the U candidate  *)
op u_check (r : R) (P : int -> R) (s : int -> int -> int) : bool.

(* check whether the table could be computed *)
op table_check (P : int -> R) (r : R) : bool.


op helperI_pure (l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argic : int) (argcc : R) 
    = (iteri l (fun j (acc : bool * R) 
        => (acc.`1 /\ predicate acc.`2 (argT j (args j argic)) , acc.`2 %%% argT j (args j argic))) (true, argcc)).

  
op multiScalarMulII_pure (T l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argu : R) (argw : int)
    = (iteri T (fun i (acc : bool * R) 
        => let r = helperI_pure l argT args i ((2 ^ argw) *** acc.`2) in (acc.`1 /\ r.`1, r.`2)) (true, argu)).






module SimpleComp = {

  proc doubleLoop(p : R, w : int) = {
      var cnt;
      cnt <- 0;
      while (cnt < w) {
        p <- p +++ p;
        cnt <- cnt + 1;
      }
      return p;
  }

  proc completeAddLoop(acc : R, table : int -> int-> R, ic : int, s : int -> int -> int) = {
      var jc, aux, vahe;

      aux <- witness;
      jc <- 0;
      vahe <- acc;
      while (jc < l) {
        aux <- table jc (s jc ic);
        vahe <- vahe +++ aux;

        jc <- jc + 1;
      }
      return vahe;
  }



  proc incompleteAddLoop(acc : R, table : int -> int-> R, ic : int, s : int -> int -> int) =    {
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


  proc multiScalarMulMain_Perfect(P : int -> R, s : int -> int -> int, U : R) = {
    var v, acc, aux, result : R;
    var table : int -> int -> R;
    var ic, jc, cnt : int;
   
    v     <- (2 ^ w - 1) *** U;
    table <- fun (j i : int) => (i *** (P j)) +++ - v;
    acc   <- l *** U;

    ic <- 0;
    while (ic < T) {
      acc <@ doubleLoop(acc,w);
      acc <@ completeAddLoop(acc, table, ic, s);
      ic <- ic + 1;
    }
    
    result <- acc +++ (- (l *** U));
    return result;
  }



  proc multiScalarMulMain_Opt(P : int -> R, s : int -> int -> int, U : R) = {
    var acc, aux, result : R;
    var table;
    var ic, jc, cnt : int;
    var flag, flagaux : bool;
    flag    <- true;
    flagaux <- true;

    table  <- perfect_table_pure P U;

    acc     <- l *** U;
    ic      <- 0;
    while (ic < T) {
      acc <@ doubleLoop(acc,w);
      (flagaux, acc) <@ incompleteAddLoop(acc, table, ic, s);
      flag <- flag && flagaux;
      ic <- ic + 1;
    }    
    return (flag, acc);
  }


  proc multiScalarMulMain_Opt_Corrected(P : int -> R, s : int -> int -> int, U : R) = {
    var result, flag;
    flag   <- u_check U P s;
    result <@ multiScalarMulMain_Opt(P,s,U);
    return (flag /\ result.`1, result.`2 +++ (- (l *** U)));
  }

  proc multiScalarMul_Fun(P : int -> R, s : int -> int -> int) = {
    var u_cand, flag, result, table;

    u_cand <$ r_distr;

   (* check u *)
   flag   <- u_check u_cand P s;

   table  <- perfect_table_pure  P (u_cand);

   result <- multiScalarMulII_pure T l table s (l *** u_cand) w;

   return (flag /\ result.`1, result.`2 +++ (- (l *** u_cand)));
  }


}.


module type UCompute = {
  proc run() : R
}.



module UniformU : UCompute = {
   proc run() = {
     var u_cand;
     u_cand <$ r_distr;
     return u_cand;
   }
}.



module NestedLoops(U : UCompute) = {

  proc multiScalarMul(P : int -> R, s : int -> int -> int) = {
    var u_cand : R;
    var flag, flagaux : bool;
    var result;

    (* choose a point (uniformly for completeness, adversarially for soundness *)
    u_cand <@ U.run(); 
    (* perform the checks on U  *)
    (* flag   <- u_check u_cand P s; *)

    (* double and add loops  *)
    result <@ SimpleComp.multiScalarMulMain_Opt_Corrected(P, s, u_cand);
    return result;
  }
}.



module MultiScalarMul(O : OutCalls) = {

  proc multiScalarMul(P : int -> R, s : int -> int -> int) = {
    var u_cand : Point;
    var flag : bool;
    var result;

    u_cand <@ O.getU();
    flag <- ! idF u_cand && onCurve u_cand;

    result <@ SimpleComp.multiScalarMulMain_Opt_Corrected(P, s, embed u_cand);
    (* result <@ multiScalarMulI(P,s,embed u_cand); *)

    return (flag /\ result.`1 , result.`2);
  }


}.


op multiScalarMulR  (s : int -> int -> int) (P : int -> R) 
  : R
 = iteri T 
     (fun i acc1 => acc1 +++ 
       iteri l
         (fun j acc2 => 
          acc2 +++ (2 ^ (w * (T - 1 - i)) * s j i) *** (P j)) idR
        ) idR.






lemma doublewtimes_spec_ph argP argw :
 phoare [ SimpleComp.doubleLoop : arg = (argP, argw) /\
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
 hoare [ SimpleComp.doubleLoop : arg = (argP, argw) /\
   0 <= argw  ==>  res = (2 ^ argw) *** argP  ].
conseq (doublewtimes_spec_ph argP argw).   
qed.   


    

lemma helper_specR_ph2 argcc argT argic args  : 
 phoare [ SimpleComp.completeAddLoop : arg = (argcc, argT, argic,  args) 
     ==>  res = iteri l (fun j acc => acc +++ argT j (args j argic)) argcc ] = 1%r.
proc.
while (0 <= jc 
 /\ jc <= l 
 /\ (acc, table, ic,  s) = (argcc, argT, argic, args) 
 /\ vahe =    iteri jc (fun j acc => acc +++ argT j (args j argic)) acc) (l - jc).
move => z.
wp. skip. progress. smt(). smt(). rewrite iteriS. smt().
   simplify.
smt(op_assoc).
smt().   
   wp. skip. progress. smt(l_pos). 
rewrite iteri0. auto.
smt(op_id).
smt().
smt().
qed.   

   
lemma helper_specR_ph argcc argT argic args  : 
 phoare [ SimpleComp.completeAddLoop : arg = (argcc, argT, argic,  args) 
     ==>  res = argcc +++  iteri l (fun j acc => acc +++ argT j (args j argic)) idR ] = 1%r.
proc.
while (0 <= jc 
 /\ jc <= l 
 /\ (acc, table, ic,  s) = (argcc, argT, argic, args) 
 /\ vahe = acc +++   iteri jc (fun j acc => acc +++ argT j (args j argic)) idR) (l - jc).
move => z.
wp. skip. progress. smt(). smt(). rewrite iteriS. smt().
   simplify.
smt(op_assoc).
smt().   
   wp. skip. progress. smt(l_pos). 
rewrite iteri0. auto.
smt(op_id).
smt().
smt().
qed.   


lemma helper_specR_total  : 
  phoare [ SimpleComp.completeAddLoop : true ==>  true ] = 1%r.
proc*.
exists*  acc, table, ic, s.
elim*. move => accV tableV icV sV.        
call (helper_specR_ph accV tableV icV sV).
auto.
qed.    


lemma helper_specR argcc argT argic args  : 
 hoare [ SimpleComp.completeAddLoop : arg = (argcc, argT, argic,  args) 
     ==>  res = argcc +++  iteri l (fun j acc => acc +++ argT j (args j argic)) idR ].
conseq (helper_specR_ph argcc argT argic args).   
progress.
qed.   


lemma multiscalarR_spec argP args argU : 
 hoare [ SimpleComp.multiScalarMulMain_Perfect : 
  arg = (argP, args, argU) 
     ==>  res = (multiScalarMulR  args argP)  ].
proc. wp.
while (0 <= ic
 /\ (2 ^ w - 1) *** U = v
 /\ table = (fun (j i : int) =>  (i *** (P j)) +++ - v)
 /\ ic <= T
 /\ acc = ((iteri ic
            (fun i acc1 => acc1 +++
              (iteri l
                 (fun j acc2 => acc2 +++ (2 ^ (w * (ic - 1 - i)) * s j i) *** (P j)) idR)
                 ) idR)) +++ l *** U).
wp.
ecall (helper_specR acc table ic s). simplify.
wp.
ecall (doublewtimes_spec acc w). skip. progress. smt(w_pos).
smt(). smt().
   rewrite mul_plus_distr.
rewrite iteriZ.           smt().
simplify.
have -> : iteri ic{hr}
  (fun (i : int) (acc0 : R) =>
     acc0 +++
     2 ^ w ***
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (ic{hr} - 1 - i)) * s{hr} j i *** P{hr} j) idR)
  idR
     = iteri ic{hr}
  (fun (i : int) (acc0 : R) =>
     acc0 +++
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (ic{hr}  - i )) * s{hr} j i *** P{hr} j) idR)
  idR.
apply eq_iteri.
progress.
rewrite iteriZ. smt(l_pos). congr.
     apply eq_iteri. move => j acc.
     progress. congr.
      have ->: 2 ^ w *** (2 ^ (w * (ic{hr} - 1 - i)) * s{hr} j i *** P{hr} j)
                = 2 ^ w * 2 ^ (w * (ic{hr} - 1 - i)) * s{hr} j i *** P{hr} j .
  rewrite mulsc. smt. smt().
        rewrite - exprD_nneg. smt(w_pos). smt(w_pos). smt().
pose v := (2 ^ w - 1) *** U{hr}.
have -> : iteri l
  (fun (j : int) (acc0 : R) => acc0 +++ (s{hr} j ic{hr} *** P{hr} j +++ -v))
  idR = iteri l
  (fun (j : int) (acc0 : R) => acc0 +++ (s{hr} j ic{hr} *** P{hr} j)) idR +++
     iteri l (fun (j : int) (acc0 : R) => acc0 +++ -v) idR.
rewrite - iteriZZ. simplify.
smt(l_pos). apply eq_iteri.  progress. smt.
simplify.
rewrite  iteriZZZ.
simplify. smt(l_pos).
rewrite kik .
have ->: (2 ^ w *** (l *** U{hr}) +++ l *** -v) = l *** U{hr}.
    rewrite /v.
  rewrite  mulsc. smt.
  have -> : l *** - (2 ^ w - 1) *** U{hr}
    = (l * - (2 ^ w - 1)) *** U{hr}. rewrite  nmul_mul.  rewrite neg_mul. auto.
   rewrite - nplus_dist. congr. smt().
rewrite iteriS.
smt(). simplify.
have ->: 2 ^ 0 = 1. smt(@Int).
smt().
wp. 
skip. progress. smt(T_pos). 
rewrite iteri0. auto. smt.
rewrite /multiScalarMulInt.
have -> : ic0 = T. smt().
simplify.
  have ->: iteri T
  (fun (i : int) (acc1 : R) =>
     acc1 +++
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (T - 1 - i)) * s{hr} j i *** P{hr} j) idR) idR +++
l *** U{hr} +++ - l *** U{hr}
       = iteri T
  (fun (i : int) (acc1 : R) =>
     acc1 +++
     iteri l
       (fun (j : int) (acc2 : R) =>
          acc2 +++ 2 ^ (w * (T - 1 - i)) * s{hr} j i *** P{hr} j) idR) idR +++
  (l *** U{hr} +++ - l *** U{hr} ).
smt(op_assoc).
rewrite op_inv.
  rewrite op_id.
  rewrite /multiScalarMulR.
auto.
qed.


lemma multiscalarR_spec_ph argP args argU : 
 phoare [ SimpleComp.multiScalarMulMain_Perfect : 
  arg = (argP, args, argU) 
     ==>  res = (multiScalarMulR  args argP)  ] = 1%r.
phoare split ! 1%r 0%r. auto.
   proc. wp.
while true (T - ic). progress.
wp.
exists* acc, table, ic, s.
elim*. move => accV tableV icV sV.
call helper_specR_total.   
call (_: arg = (accV, Top.w) ==> true).
proc*. call (doublewtimes_spec_ph accV Top.w).
skip. progress. smt(w_pos). skip.
progress.
smt().
wp. 
skip. progress. smt().
hoare. simplify.   
apply multiscalarR_spec.
qed.
