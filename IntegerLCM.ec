require import AllCore IntDiv StdOrder.
import Ring.IntID IntOrder.

(* Binary LCM, extended to all integers with lcm(0,a)=0. *)
op lcm_pair (a b : int) = `|a * (b %/ gcd a b)|.

lemma lcm_pair_nonnegative a b : 0 <= lcm_pair a b.
proof. rewrite /lcm_pair. smt(). qed.

lemma lcm_pair_divides a b x :
  lcm_pair a b %| x <=> a %| x /\ b %| x.
proof.
rewrite /lcm_pair dvdz_norml.
case ((a,b)=(0,0)).
+ move=> [-> ->]. by rewrite /= dvd0z.
move=> Hab.
have Hg : gcd a b<>0 by rewrite gcd_eq0.
have Ha : a %/ gcd a b * gcd a b=a by apply divzK; exact (dvdz_gcdl a b).
have Hb : b %/ gcd a b * gcd a b=b by apply divzK; exact (dvdz_gcdr a b).
have E : a * (b %/ gcd a b) = (a %/ gcd a b) * b by smt().
split.
+ move=> H.
  split.
  + apply (dvdz_trans (a * (b %/ gcd a b)) a x); last exact H.
    apply dvdz_mulr. exact (dvdzz a).
  + apply (dvdz_trans (a * (b %/ gcd a b)) b x); last exact H.
    rewrite E. apply dvdz_mull. exact (dvdzz b).
+ move=> [/dvdzP [ka Hxa] /dvdzP [kb Hxb]].
  have [r s Hbez] := Bachet_Bezout a b.
  apply/dvdzP. exists (r*kb+s*ka).
  have Hprod : (r*kb+s*ka)*(a*(b %/ gcd a b))*gcd a b=x*gcd a b.
  + have E1 : (r*kb+s*ka)*(a*(b %/ gcd a b))*gcd a b =
      (r*kb+s*ka)*a*(b %/ gcd a b*gcd a b) by ring.
    rewrite E1 Hb. smt().
  smt().
qed.

(* Fold over indices 0 <= i < n. Empty and negative lengths give 1. *)
op LCM (M : int -> int) (n : int) = iteri n (fun i acc => lcm_pair acc (M i)) 1.

lemma LCM_empty M n : n<=0 => LCM M n=1.
proof. move=> Hn. by rewrite /LCM iteri0. qed.

lemma LCM_step M n : 0<=n => LCM M (n+1)=lcm_pair (LCM M n) (M n).
proof. move=> Hn. by rewrite /LCM iteriS. qed.

lemma LCM_nonnegative M n : 0<=LCM M n.
proof.
elim/natind: n=> [n Hn|n Hn IH].
+ by rewrite LCM_empty.
+ rewrite LCM_step //. exact (lcm_pair_nonnegative _ _).
qed.

lemma LCM_divides M n x : LCM M n %| x <=> forall i, 0<=i<n => M i %| x.
proof.
elim/natind: n=> [n Hn|n Hn IH].
+ rewrite LCM_empty // dvd1z. smt().
+ rewrite LCM_step // lcm_pair_divides IH. smt().
qed.

lemma lcm_pair_zero a b : lcm_pair a b=0 <=> a=0 \/ b=0.
proof.
rewrite /lcm_pair normr0P mulf_eq0.
have Hb := divzK (gcd a b) b (dvdz_gcdr a b).
smt(div0z).
qed.

lemma LCM_single M : LCM M 1 = `|M 0|.
proof. by rewrite (@LCM_step M 0) 1:/# LCM_empty 1:/# /lcm_pair gcd1z divz1 /=. qed.

lemma LCM_zero M n : LCM M n=0 <=> exists i, 0<=i<n /\ M i=0.
proof.
elim/natind: n=> [n Hn|n Hn IH].
+ rewrite LCM_empty //. smt().
+ rewrite LCM_step // lcm_pair_zero IH. smt().
qed.

lemma LCM_positive M n :
  (forall i, 0<=i<n => M i<>0) => 0<LCM M n.
proof. smt(LCM_nonnegative LCM_zero). qed.

lemma LCM_common_multiple M n i : 0<=i<n => M i %| LCM M n.
proof. have H := LCM_divides M n (LCM M n). smt(dvdzz). qed.

lemma LCM_least_positive M n x :
  0<x => (forall i, 0<=i<n => M i %| x) => LCM M n<=x.
proof. move=> Hx HM. apply dvdn_le; first exact Hx. by rewrite LCM_divides. qed.

(* This includes equal residues, not only divisibility / zero residues. *)
lemma LCM_congruence M n x y :
  (forall i, 0<=i<n => eqm (M i) x y) <=> eqm (LCM M n) x y.
proof.
have H := LCM_divides M n (x-y).
smt(eqz_mod_dvd).
qed.
