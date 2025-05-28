require import AllCore Int IntDiv List StdOrder Bool Distr.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

require import MultiScalarMul_Abstract_Setup IterationProps.


(* params  *)
op T : int.
op l : int.
op w : int.

(* params are positive  *)
axiom w_pos : 0 < w.
axiom l_pos : 0 < l.
axiom T_pos : 0 < T.


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
  proc getU() : R
}.



(* check the U candidate  *)
op u_check (r : R) (P : int -> R) (s : int -> int -> int) : bool.

op incompleteAddLoop (l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argic : int) (argcc : R) 
    = (iteri l (fun j (acc : bool * R) 
        => (acc.`1 /\ xdiff acc.`2 (argT j (args j argic)), 
             acc.`2 %%% argT j (args j argic))) (true, argcc)).


op completeAddLoop (l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argic : int) (argcc : R) 
    = (iteri l (fun j (acc : bool * R) 
        => (acc.`1 /\ xdiff acc.`2 (argT j (args j argic)), 
             acc.`2  +++ argT j (args j argic))) (true, argcc)).

  
op multiScalarMul (T l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argu : R) (argw : int)
    = (iteri T (fun i (acc : bool * R) 
        => let r = incompleteAddLoop l argT args i ((2 ^ argw) *** acc.`2) in 
         (acc.`1 /\ r.`1, r.`2)) (true, argu)).

op multiScalarMul_Complete (T l : int) (argT : int -> int -> R)
  (args : int -> int -> int) (argu : R) (argw : int)
    = (iteri T (fun i (acc : bool * R) 
        => let r = completeAddLoop l argT args i ((2 ^ argw) *** acc.`2) in 
         (acc.`1 /\ r.`1, r.`2)) (true, argu)).


op multiScalarMul_Simpl  (s : int -> int -> int) (P : int -> R) (ic jc  : int)
  : R
 = iteri ic
     (fun i acc1 => acc1 +++ 
       iteri jc
         (fun j acc2 => 
          acc2 +++ (2 ^ (w * (ic - 1 - i)) * s j i) *** (P j)) idR
        ) idR.







module UniformU : OutCalls = {
   proc getU() = {
     var u_cand;
     u_cand <$ r_distr;
     return u_cand;
   }
}.



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
      var jc, aux, vahe, flag;

      aux <- witness;
      flag <- true;
      jc <- 0;
      vahe <- acc;
      while (jc < l) {
        aux <- table jc (s jc ic);
        flag <- flag /\ xdiff vahe aux;
        vahe <- vahe +++ aux;

        jc <- jc + 1;
      }
      return (flag, vahe);
  }



  proc incompleteAddLoop(acc : R, table : int -> int-> R, ic : int, s : int -> int -> int) =    {
      var jc, aux, vahe, flag;
    
      aux <- witness;
      flag <- true;
      jc <- 0;
      vahe <- acc;
      while (jc < l) {
        aux <- table jc (s jc ic);
        flag <- flag /\ xdiff vahe aux;
        vahe <- (vahe %%% aux);

        jc <- jc + 1;
      }
      return (flag, vahe);
  }


  proc multiScalarMulMain_Perfect_Helper(P : int -> R, s : int -> int -> int, U : R, Targ : int) = {
    var v, acc, aux, result : R;
    var table : int -> int -> R;
    var ic, jc, cnt : int;
    var flagaux, flag : bool;
    flagaux <- true;
    flag <- true;
   
    v     <- (2 ^ w - 1) *** U;
    table <- perfect_table_pure P U;
    acc   <- l *** U;

    ic <- 0;
    while (ic < Targ) {
      acc <@ doubleLoop(acc,w);
      (flagaux, acc) <@ completeAddLoop(acc, table, ic, s);
      flag <- flag && flagaux;
      ic <- ic + 1;
    }
    
    (* result <- acc +++ (- (l *** U)); *)
    return (flag, acc);
  }

  proc multiScalarMulMain_Perfect(P : int -> R, s : int -> int -> int, U : R) = {
     var result, flag;
     flag   <- u_check U P s;    
     result <@ multiScalarMulMain_Perfect_Helper(P,s,U,T);
     return  (flag /\ result.`1, result.`2 +++ (- (l *** U)));
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
    table  <- perfect_table_pure  P u_cand;
    result <- multiScalarMul T l table s (l *** u_cand) w;

    return (flag /\ result.`1, result.`2 +++ (- (l *** u_cand)));
  }


  proc multiScalarMul_Fun2(P : int -> R, s : int -> int -> int) = {
    var u_cand, flag, result, table;

    u_cand <$ r_distr;

   (* check u *)
    flag   <- u_check u_cand P s;
    table  <- perfect_table_pure  P u_cand;
    result <- multiScalarMul_Complete T l table s (l *** u_cand) w;

    return (flag /\ result.`1, result.`2 +++ (- (l *** u_cand)));
  }

}.


module MultiScalarMul(O : OutCalls) = {
  proc run(P : int -> R, s : int -> int -> int) = {
    var u_cand, result;
    u_cand <@ O.getU();
    result <@ SimpleComp.multiScalarMulMain_Opt_Corrected(P, s, u_cand);
    return result;
  }

  proc run_perfect(P : int -> R, s : int -> int -> int) = {
    var u_cand, result;
    u_cand <@ O.getU();
    result <@ SimpleComp.multiScalarMulMain_Perfect(P, s, u_cand);
    return result;
  }
}.


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

   
lemma helper_specR_ph argcc argT argic args  : 
 phoare [ SimpleComp.completeAddLoop : arg = (argcc, argT, argic,  args) 
     ==>  res.`2 = argcc +++  iteri l (fun j acc => acc +++ argT j (args j argic)) idR ] = 1%r.
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


lemma doubleLoop_total  : 
  phoare [ SimpleComp.doubleLoop : true ==>  true ] = 1%r.
proc.
while true (w - cnt). auto.
smt().
wp. auto. smt().
qed.    


lemma helper_specR argcc argT argic args  : 
 hoare [ SimpleComp.completeAddLoop : arg = (argcc, argT, argic,  args) 
     ==>  res.`2 = argcc +++  iteri l (fun j acc => acc +++ argT j (args j argic)) idR ].
conseq (helper_specR_ph argcc argT argic args).   
progress.
qed.   


lemma multiscalarR_helper_spec argP args argU  argT: 0 <= argT =>
 hoare [ SimpleComp.multiScalarMulMain_Perfect_Helper : 
  arg = (argP, args, argU, argT) 
     ==>  res.`2 = (multiScalarMul_Simpl args argP argT l ) +++ l *** argU  ].
proof. move => argTp.
proc. wp.
while (0 <= ic /\ argT = Targ
 /\ (2 ^ w - 1) *** U = v
 /\ table = (fun (j i : int) =>  (i *** (P j)) +++ - v)
 /\ ic <= argT
 /\ acc = ((iteri ic
            (fun i acc1 => acc1 +++
              (iteri l
                 (fun j acc2 => acc2 +++ (2 ^ (w * (ic - 1 - i)) * s j i) *** (P j)) idR)
                 ) idR)) +++ l *** U).
wp.
ecall (helper_specR acc table ic s). simplify.
wp.
ecall (doublewtimes_spec acc w). skip. progress. smt(w_pos).
smt(). smt(). rewrite H3.
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
skip. progress.  
rewrite iteri0. auto. smt.
rewrite /multiScalarMulInt.
have -> : ic0 = Targ{hr}. smt().
simplify. 
rewrite /multiScalarMul_Simpl.
    reflexivity.
qed.


lemma multiscalarR_helper_spec_ph argP args argU argT : 0 <= argT
 => phoare [ SimpleComp.multiScalarMulMain_Perfect_Helper : 
  arg = (argP, args, argU, argT)  
     ==>  res.`2 = (multiScalarMul_Simpl args argP argT l) +++ l *** argU ] = 1%r.
move => pp.
phoare split ! 1%r 0%r. auto.
   proc. wp.
while true (argT - ic). progress.
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
conseq (multiscalarR_helper_spec argP args argU argT _). auto.
qed.


lemma multiscalarR_spec_ph argP args argU  : 
 phoare [ SimpleComp.multiScalarMulMain_Perfect : 
  arg = (argP, args, argU) 
     ==>  res.`2 = (multiScalarMul_Simpl args argP T l) ] = 1%r.
proc.   
call (multiscalarR_helper_spec_ph argP args argU T). auto.
progress. smt(T_pos).
wp. skip. auto.
progress. rewrite H.
smt.   
qed.


lemma compelteAddLoop_ph argcc argT argic args :
 phoare [ SimpleComp.completeAddLoop : arg = (argcc, argT, argic,  args) 
     ==>  res = (completeAddLoop l argT args argic argcc) ] = 1%r.    
proc.
wp.   
while (0 <= jc 
 /\ jc <= l 
 /\ (acc, table, ic,  s) = (argcc, argT, argic, args) 
 /\ (flag, vahe) =  (iteri jc (fun j (acc : bool * R) => (acc.`1 /\ xdiff acc.`2 (argT j (args j argic)) , acc.`2 +++ argT j (args j argic))) (true, argcc))) (l - jc).
move => z.
wp. skip. progress. smt(). smt(). rewrite iteriS. smt().
   simplify.
   rewrite /xdiff. 
pose xxx := (iteri jc{hr}
     (fun (j : int) (acc0 : bool * R) =>
        (acc0.`1 /\
         xof acc0.`2 <> xof (table{hr} j (s{hr} j ic{hr})) && acc0.`2 <> idR,
         acc0.`2 +++ table{hr} j (s{hr} j ic{hr}))) (true, acc{hr})).
pose yyy := (iteri jc{hr}
       (fun (j : int) (acc0 : R) => acc0 %%% table{hr} j (s{hr} j ic{hr}))
       acc{hr}).     smt().
 smt().
(* smt(op_assoc). *)
(* smt(). *)   
   wp. skip. progress. smt(l_pos). 
rewrite iteri0. auto. auto.
(* rewrite iteri0. auto. auto. *)
smt().   
rewrite H2.
         smt().
qed.  


lemma compelteAddLoop_h argcc argT argic args  : 
 hoare [ SimpleComp.completeAddLoop : arg = (argcc, argT, argic,  args) 
     ==>  res = (completeAddLoop l argT args argic argcc) ].
conseq (compelteAddLoop_ph argcc argT argic args). 
qed.


lemma multm_spec_h argP args argU  argT : 0 <= argT =>
 hoare [ SimpleComp.multiScalarMulMain_Perfect_Helper : arg = (argP, args, argU, argT)   
  ==>  res = (multiScalarMul_Complete argT l (perfect_table_pure argP argU) args (l *** argU) w) ].
move => pp.
proc. 
while (argT = Targ /\
  0 <= ic 
  /\ ic <= argT
  /\ (U, table, s) = (argU, (perfect_table_pure argP argU), args) 
  /\ (flag, acc) = (multiScalarMul_Complete ic l ((perfect_table_pure argP argU)) args (l *** argU) w)
 ) .
wp.
ecall (compelteAddLoop_h acc (perfect_table_pure argP argU) ic args).
ecall (doublewtimes_spec acc w). 
skip.
progress. smt(w_pos).
smt(). smt(). 
rewrite /multiScalarMul_Complete. rewrite iteriS. smt(). smt(). 
wp. skip. progress. 
rewrite /multiScalarMul_Complete. rewrite iteri0.
auto. auto. 
have -> : Targ{hr} = ic0. smt(T_pos).
auto.
qed. 


lemma multm_spec_ph2 argP args argU argT : 0 <= argT =>
 phoare [ SimpleComp.multiScalarMulMain_Perfect_Helper : arg = (argP, args, argU, argT)   
  ==>  res = (multiScalarMul_Complete argT l (perfect_table_pure argP argU) args (l *** argU) w)   ] = 1%r.
move => pp.
phoare split ! 1%r 0%r. auto.
proc. while true (argT - ic). auto.
call helper_specR_total.
call doubleLoop_total.
skip. smt().
wp. skip. smt().
hoare.
proc*. 
call (multm_spec_h argP args argU argT pp).
auto.
qed.


op gg (s : int -> int -> int) (P : int -> R) (i : int) (u : R) :  R 
  = (multiScalarMul_Simpl s P i l) +++ l *** u.


lemma oook argP (r : R) (argic : int)  args start : forall (n : int), 0 <= n =>
   (iteri n
   (fun (i1 : int) (acc0 : bool * R) =>
      (acc0.`1 /\ xdiff acc0.`2 (perfect_table_pure argP r i1 (args i1 argic)),
       acc0.`2 +++ perfect_table_pure argP r i1 (args i1 argic)))
   (true, start)).`2
    =    (iteri n
   (fun (i1 : int) (acc0 : R) =>
      (acc0 +++ perfect_table_pure argP r i1 (args i1 argic)))
     start).
apply intind. progress. 
rewrite iteri0. auto.
  rewrite iteri0. auto. auto.
progress.
rewrite iteriS. auto.
  rewrite iteriS. auto.
simplify.   rewrite H0. auto.
qed.  

  
op hh (args : int -> int -> int)  (argP : int -> R)  (argic : int) (l : int) (u : R) =  2 ^ w *** gg args argP argic u +++  (iteri l
   (fun (i1 : int) (acc0 : R) =>
      (acc0 +++ perfect_table_pure argP u i1 (args i1 argic)))
   idR).


lemma comeqsimp args argP argic l r : 0 <= l =>
  (iteri l
   (fun (i1 : int) (acc0 : bool * R) =>
      (acc0.`1 /\ xdiff acc0.`2 (perfect_table_pure argP r i1 (args i1 argic)),
       acc0.`2 +++ perfect_table_pure argP r i1 (args i1 argic)))
   (true, 2 ^ w *** gg args argP argic r)).`2
 = hh args argP argic l r .
proof. move => pp.
rewrite /hh. rewrite oook. assumption.
rewrite (iteriZZZZZ (fun i1 => perfect_table_pure argP r i1 (args i1 argic))  (2 ^ w *** gg args argP argic r) l _ ). assumption. smt.
qed.


lemma muleqsimp2 argT s u P: 0 <= argT =>
   gg s P argT u = (multiScalarMul_Complete argT l (perfect_table_pure P u) s (l *** u) w).`2.
proof. move => pp.
rewrite /gg.
case (multiScalarMul_Simpl s P argT l +++ l *** u = (multiScalarMul_Complete argT l (perfect_table_pure P u) s (l *** u) w).`2). 
trivial.
move => ineq.
have : forall &m, 
  Pr[ SimpleComp.multiScalarMulMain_Perfect_Helper(P,s, u,argT) @&m :
     gg s P argT u = (multiScalarMul_Complete argT l (perfect_table_pure P u) s (l *** u) w).`2  ] = 1%r.
     progress.
     have ->: 1%r = Pr[ SimpleComp.multiScalarMulMain_Perfect_Helper(P,s, u,argT) @&m :
         res.`2 = gg s P argT u ].
    byphoare (_: arg = (P, s, u,argT) ==> _).
    conseq (multiscalarR_helper_spec_ph P s u argT _). assumption. auto. auto.
    rewrite /gg. 
    byequiv.
    proc*.
    call {2} (multm_spec_ph2 P s u argT _). 
    call {1} (multiscalarR_helper_spec_ph P s u argT _). skip. 
    progress. rewrite  H0. auto. smt(). auto. auto. 
   have : exists &m, true. smt().
    elim. move => &h. auto.
    move => _. rewrite /gg. move => p.
    have : Pr[SimpleComp.multiScalarMulMain_Perfect_Helper(P, s, u, argT) @ &h :
       false] = 1%r.
     rewrite -  ineq. apply (p &h).
  smt(@Distr).
qed.



axiom u_check_for_table U P s : u_check U P s =>
  forall i j, perfect_table_pure P U i j <> idR.

lemma multieqs2 argP args argU  :
 equiv [ SimpleComp.multiScalarMulMain_Perfect 
        ~ SimpleComp.multiScalarMulMain_Opt_Corrected :
  arg{2} = (argP, args, argU) /\ ={P,s,U} 
     ==>  (res{2}.`1 => (res{1} = res{2})) /\ (res{1}.`1 => res{2}.`1)   ].
proc.
wp.
inline SimpleComp.multiScalarMulMain_Opt.
inline   SimpleComp.multiScalarMulMain_Perfect_Helper.
       wp.
while ((flag0{2} /\ u_check U{2} P{2} s{2} =>  ={table,acc,U,s,flag0} /\ (forall i j, table{2} i j <> idR)) /\ (flag0{2} => flagaux{2}) /\ ={ic} /\ s0{1} = s0{2}
 /\ table{2} = perfect_table_pure P{2} U{2} /\ Targ{1} = T /\ (flag0{1} /\ u_check U{2} P{2} s{2} => flag0{2})  ).
wp.
inline SimpleComp.completeAddLoop.
inline SimpleComp.incompleteAddLoop.   
wp.
while ((flag0{2} /\ flag1{2} /\ u_check U{2} P{2} s{2} =>  ={flag1, vahe, acc0,table0,aux0,ic0} /\ (forall i j, table0{2} i j <> idR) /\ vahe{2} <> idR) /\ ={jc0} /\ s1{1} = s1{2} /\ table{2} = table0{2} 
 /\ table{2} = perfect_table_pure P{2} U{2}  /\ Targ{1} = T  /\ (flag0{2} /\ flag1{1} /\ u_check U{2} P{2} s{2} => flag1{2})).
 wp. skip. progress.  smt().  
       have -> : vahe{2} = vahe{1}. smt(). 
rewrite same_res. 
  smt().
  smt().
  smt().
  smt().
  smt().
     smt().
     smt().
     smt().
     smt().
apply opt_never_id. smt(). smt().
smt(). smt(). smt().
wp.
ecall {1} (doublewtimes_spec_ph acc{1} w).
ecall {2} (doublewtimes_spec_ph acc{2} w).
skip. progress. 
smt(w_pos). smt(). smt(). smt().
smt().  
apply no_order_two_elems. smt(w_pos). 
smt(). smt(). smt().
       smt(). smt().
apply (u_check_for_table U{2} P{2} s{2} _ i j).        auto. smt(). smt().
       wp. 
 skip. progress.
   apply (u_check_for_table U{2} P{2} s{2} H i j).       
smt(). smt(). smt().
 qed.
