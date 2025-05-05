
require import AllCore IntDiv CoreMap List.

require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

(*  

   P := (beta, x, y) 
   1/ subset by "onCurve"
   2/ equiv. rel by  
 
       2.1/ non unique representation of "x" and "y"
       2.2/ all variations of identity point

*)

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

type Point.

op onCurve : Point -> bool.
op idF     : Point -> bool.
op embed   : Point -> R.

op perfect_table_pure  parg varg = 
 (fun (j i : int) =>  (i *** (parg j)) +++ - varg).


op r_distr : R distr.

module type OutCalls = {
  proc getU() : Point
  proc getUniformU() : R
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
    var u_cand : Point;
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

  proc multiScalarMul_Completeness(P : int -> R, s : int -> int -> int) = {
    var u_cand : R;
    var flag : bool;
    var result;

    u_cand <@ O.getUniformU();
    result <@ multiScalarMulI(P,s,u_cand);
    return result;
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


}.


op multiScalarMulR  (s : int -> int -> int) (P : int -> R) 
  : R
 = iteri T 
     (fun i acc1 => acc1 +++ 
       iteri l
         (fun j acc2 => 
          acc2 +++ (2 ^ (w * (T - 1 - i)) * s j i) *** (P j)) idR
        ) idR.



lemma qiq : forall a, 0 <= a => forall (c : int), forall (b : R),
   a *** b +++ c *** b = (a + c) *** b.
apply natind. progress. smt.
progress. rewrite nplus_dist. auto.
have ->: (n + 1 + c) = ((n + c) + 1). smt().
rewrite nplus_dist. 
rewrite - H0. smt().    
smt(op_comm op_assoc).
qed.    



