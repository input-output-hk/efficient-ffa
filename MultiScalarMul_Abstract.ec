
require import AllCore IntDiv CoreMap List.

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


(* params  *)
op T : int.
op l : int.
op w : int.

(* params are positive  *)
axiom w_pos : 0 < w.
axiom l_pos : 0 < l.
axiom T_pos : 0 < T.

op onCurve : F -> bool.
op idF     : F -> bool.
op embed   : F -> R.


lemma nosmt addass (a b c : int) : a + (b + c) = (a + b) + c.    by smt(). qed.
lemma nosmt muldist (a b c : int) : a * (b + c) = a * b + a * c. by smt(). qed.
lemma nosmt eqsym ['a] (a b : 'a) : a = b => b = a.              by smt(). qed.

lemma kik  (a b c d : R) :  a +++ b +++ (c +++ d) = a +++ c +++ (b +++ d). 
 by smt(op_assoc op_comm). qed.

    
lemma qiq : forall a, 0 <= a => forall (c : int), forall (b : R),
   a *** b +++ c *** b = (a + c) *** b.
apply natind. progress. smt.
progress. rewrite nplus_dist. auto.
have ->: (n + 1 + c) = ((n + c) + 1). smt().
rewrite nplus_dist. 
rewrite - H0. smt().    
smt(op_comm op_assoc).
qed.    

    

module type OutCalls = {
  proc getU() : F
  proc getT(P : int -> R, v : R) : int -> int -> R
  proc getPT(P : int -> R, v : R) : bool * (int -> int -> R)
}.

module MultiScalarMul(O : OutCalls) = {

  proc helper(acc : int, table : int -> int-> int, ic : int, P : int -> int, s : int -> int -> int, U : int) = {
      var jc, aux, vahe;
    
      jc <- 1;
      vahe <- acc;
      while (jc < l + 1) {
        aux <- table jc (s jc ic);
        vahe <- vahe + aux;

        jc <- jc + 1;
      }
      return vahe;
  }

  proc helperR(acc : R, table : int -> int-> R, ic : int, s : int -> int -> int) = {
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

  
  proc doubleWtimes(p : R, w : int) = {
      var cnt;
      cnt <- 0;
      while (cnt < w) {
        p <- p +++ p;
        cnt <- cnt + 1;
      }
      return p;
  }


  proc multiScalarMulR(P : int -> R, s : int -> int -> int, U : R) = {
    var v, acc, aux, result : R;
    var table : int -> int -> R;
    var ic, jc, cnt : int;

   
    v     <- (2 ^ w - 1) *** U;
    table <@ O.getT(P, v);
    acc   <- l *** U;

    ic <- 0;
    while (ic < T) {
      acc <@ doubleWtimes(acc,w);
      acc <@ helperR(acc, table, ic, s);
      ic <- ic + 1;
    }
    
    result <- acc +++ (- (l *** U));
    return result;
  }



  proc helperI(acc : R, table : int -> int-> R, ic : int, s : int -> int -> int) = {
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



  proc multiScalarMulI(P : int -> R, s : int -> int -> int, U : R) = {
    var u, v, acc, aux, result : R;
    var table : int -> int -> R;
    var ic, jc, cnt : int;
    var flag, flagaux : bool;

    flag  <- true;
    flagaux <- true;
    v     <- (2 ^ w - 1) *** U;
    (flagaux, table) <@ O.getPT(P, v);
    flag <- flag && flagaux;
    acc   <- l *** U;

    ic <- 0;
    while (ic < T) {
      acc <@ doubleWtimes(acc,w);
      (flagaux, acc) <@ helperI(acc, table, ic, s);
      flag <- flag && flagaux;
      ic <- ic + 1;
    }
    
    result <- acc +++ (- (l *** U));
    return (flag, result);
  }

  proc multiScalarMul(P : int -> R, s : int -> int -> int) = {
    var u_cand : F;
    var flag : bool;
    var result;

    u_cand <@ O.getU();
    flag <- ! idF u_cand && onCurve u_cand;

    if(flag = true) {
      result <@ multiScalarMulI(P,s,embed u_cand);
    } else{
      result <- (false, witness);    
    } 


    return result;
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

section.

declare module O <: OutCalls.
declare module O_Partial <: OutCalls.

declare axiom tableP parg varg : hoare [ O.getT : arg = (parg,varg)
   ==> res = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  ].

declare axiom tablePT parg varg : hoare [ O.getPT : arg = (parg,varg)
   ==> res.`1 => (res.`2 = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  /\ (forall i j, res.`2 i j <> idR) )   ].
 
declare axiom getT_lossless : islossless O.getT.

declare axiom tableP_ph parg varg : phoare [ O.getT : arg = (parg,varg)
   ==> res = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  ] = 1%r.

declare axiom tablePT_ph parg varg : phoare [ O.getPT : arg = (parg,varg)
   ==> res.`1 => (res.`2 = (fun (j i : int) =>  (i *** (parg j)) +++ - varg)  /\ (forall i j, res.`2 i j <> idR) )   ] = 1%r.


lemma helpereqs argacc argtable argic args  : 
 equiv [ MultiScalarMul(O).helperR ~ MultiScalarMul(O).helperI : 
  arg{2} = (argacc, argtable, argic, args) /\ ={acc,table,ic,s}
       /\ (forall i j, table{1} i j <> idR)
     ==>  res{2}.`1 => (res{1} = res{2}.`2)].
proc.
while (={jc,acc,table,aux,s,ic} /\ (flag{2} => ={vahe})
 /\ (forall i j, table{1} i j <> idR)).
 wp. skip. progress.
   have -> : vahe{1} = vahe{2}. smt().
rewrite same_res. 
  smt().
  smt(). 
  smt().
  smt().
wp. skip. progress. 
qed.

    
   
lemma helper_specR_ph argcc argT argic args  : 
 phoare [ MultiScalarMul(O).helperR : arg = (argcc, argT, argic,  args) 
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
 phoare [ MultiScalarMul(O).helperR : true ==>  true ] = 1%r.
proc*.
exists*  acc, table, ic, s.
elim*. move => accV tableV icV sV.        
call (helper_specR_ph accV tableV icV sV).
auto.
qed.    


lemma helper_specR argcc argT argic args  : 
 hoare [ MultiScalarMul(O).helperR : arg = (argcc, argT, argic,  args) 
     ==>  res = argcc +++  iteri l (fun j acc => acc +++ argT j (args j argic)) idR ].
conseq (helper_specR_ph argcc argT argic args).   
progress.
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


lemma doublewtimes_spec_ph argP argw :
 phoare [ MultiScalarMul(O).doubleWtimes : arg = (argP, argw) /\
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
 hoare [ MultiScalarMul(O).doubleWtimes : arg = (argP, argw) /\
   0 <= argw  ==>  res = (2 ^ argw) *** argP  ].
conseq (doublewtimes_spec_ph argP argw).   
qed.   


lemma multiscalarR_spec argP args argU : 
 hoare [ MultiScalarMul(O).multiScalarMulR : 
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
ecall (tableP P v). wp. skip. progress. smt(T_pos).
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
 phoare [ MultiScalarMul(O).multiScalarMulR : 
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
wp. call (_:true). apply getT_lossless. 
wp. skip. progress. smt().
hoare. simplify.   
apply multiscalarR_spec.
qed.

lemma multieqs argP args argU  :
 equiv [ MultiScalarMul(O).multiScalarMulR 
        ~ MultiScalarMul(O).multiScalarMulI :
  arg{2} = (argP, args, argU) /\ ={P,s,U} /\ ={glob O}
     ==>  res{2}.`1 => (res{1} = res{2}.`2)].
proc.
wp.
while ((flag{2} => ={table,acc,U,s} /\ (forall i j, table{2} i j <> idR)) /\ (flag{2} => flagaux{2}) /\ ={ic}  ).
wp.
inline MultiScalarMul(O).helperR.
inline MultiScalarMul(O).helperI.
wp.
while ((flag{2} /\ flag0{2} => ={vahe, acc0,table0,aux0,s0,ic0} /\ (forall i j, table0{2} i j <> idR)) /\ ={jc0}).
 wp. skip. progress.
   have -> : vahe{1} = vahe{2}. smt().
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
     smt().
wp.
inline MultiScalarMul(O).doubleWtimes.
wp.
   while ((flag{2} => ={p}) /\ ={w,cnt0}). wp. skip. progress.
   smt(). wp. skip. progress.
smt(). smt(). smt(). smt(). smt(). smt().
   smt(). smt().  smt(). smt(). smt().
wp. 

ecall {1} (tableP_ph P{1} v{1} ).
ecall {2} (tablePT_ph P{2} v{2}).    

wp. skip. progress. smt(). smt().
have -> :     acc_L = acc_R. smt(). auto.
qed.

lemma multiscalarI_spec_ph argP args  argU : 
 phoare [ MultiScalarMul(O).multiScalarMulI : 
  arg = (argP, args, argU) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] = 1%r.
proof.
bypr.
progress.
have ih: 1%r = Pr[MultiScalarMul(O).multiScalarMulR(P{m}, s{m}, U{m}) @ &m 
  : res = multiScalarMulR args argP].
byphoare (_: arg = (argP, args, argU) ==> _).
conseq (multiscalarR_spec_ph argP args argU). smt(). auto.
have : Pr[MultiScalarMul(O).multiScalarMulI(P{m}, s{m}, U{m}) @ &m :
   res.`1 => res.`2 = multiScalarMulR args argP] >=
Pr[MultiScalarMul(O).multiScalarMulR(P{m}, s{m}, U{m}) @ &m :
   res = multiScalarMulR args argP].
byequiv (_: _ ==> res{2}.`1 => res{2}.`2 = res{1} ).
proc*.
ecall (multieqs argP args argU).
skip. progress. smt(). smt(). smt(). smt().
auto.
smt().
smt.
qed.

lemma multiscalarI_spec_h argP args  argU : 
 hoare [ MultiScalarMul(O).multiScalarMulI : 
  arg = (argP, args, argU) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] .
conseq (multiscalarI_spec_ph argP args argU).
qed.   


lemma multiscalar_spec_h argP args : 
 hoare [ MultiScalarMul(O).multiScalarMul : 
  arg = (argP, args) 
     ==>  res.`1 => res.`2 = (multiScalarMulR  args argP)  ] .
proc.
seq 1 : #pre.
call (_: true). auto.
sp. if.
  ecall (multiscalarI_spec_h P s (embed u_cand)).
   skip. progress.
wp. skip.
smt().
qed.   

end section.
