require import AllCore IntDiv StdOrder AuxResults.
require IntegerLCM.
import Ring.IntID IntOrder.

op two_moduli (a b : int) = fun (i : int) => if i=0 then a else b.
op three_moduli = fun (i : int) => if i=0 then 4 else if i=1 then 6 else 5.

lemma gcd_four_six : gcd 4 6=2.
proof. by rewrite -(gcd_modr 4 6) /= -(gcd_modl 4 2) /=. qed.

lemma empty_family : LCM (fun (_ : int) => 0) 0=1.
proof. by rewrite /AuxResults.LCM IntegerLCM.LCM_empty. qed.

lemma negative_length : LCM (fun (_ : int) => 0) (-3)=1.
proof. by rewrite /AuxResults.LCM IntegerLCM.LCM_empty. qed.

lemma negative_singleton : LCM (fun (_ : int) => -6) 1=6.
proof. by rewrite /AuxResults.LCM IntegerLCM.LCM_single /=. qed.

(* Shared factors are retained once: the result is 12, not the product 24. *)
lemma noncoprime_moduli : LCM (two_moduli 4 6) 2=12.
proof.
rewrite /AuxResults.LCM (@IntegerLCM.LCM_step _ 1) 1:/# IntegerLCM.LCM_single
  /two_moduli /IntegerLCM.lcm_pair /= gcd_four_six. smt().
qed.

lemma negative_moduli : LCM (two_moduli (-4) (-6)) 2=12.
proof.
rewrite /AuxResults.LCM (@IntegerLCM.LCM_step _ 1) 1:/# IntegerLCM.LCM_single
  /two_moduli /IntegerLCM.lcm_pair /= gcd_four_six. smt().
qed.

lemma repeated_moduli : LCM (two_moduli 6 6) 2=6.
proof.
rewrite /AuxResults.LCM (@IntegerLCM.LCM_step _ 1) 1:/# IntegerLCM.LCM_single
  /two_moduli /IntegerLCM.lcm_pair /= -(gcd_modr 6 6) /=. smt().
qed.

lemma zero_modulus : LCM (two_moduli 6 0) 2=0.
proof.
rewrite /AuxResults.LCM IntegerLCM.LCM_zero. exists 1. by rewrite /two_moduli /=.
qed.

lemma zero_modulus_requires_zero x :
  (forall i, 0<=i<2 => x %% two_moduli 6 0 i=0) <=> x=0.
proof. by rewrite chinese_reminder_theorem zero_modulus modz0. qed.

lemma noncoprime_divisibility x :
  (x %% 4=0 /\ x %% 6=0) <=> x %% 12=0.
proof.
have H := chinese_reminder_theorem x (two_moduli 4 6) 2.
rewrite noncoprime_moduli /two_moduli in H.
smt().
qed.

(* A small analogue of FFA's auxiliary moduli plus the field modulus. *)
lemma moduli_with_field : LCM three_moduli 3=60.
proof.
have E : IntegerLCM.LCM three_moduli 2=12.
+ rewrite (@IntegerLCM.LCM_step _ 1) 1:/# IntegerLCM.LCM_single
    /three_moduli /IntegerLCM.lcm_pair /= gcd_four_six. smt().
have G : gcd 12 5=1
  by rewrite -(gcd_modl 12 5) /= -(gcd_modr 2 5) /=.
rewrite /AuxResults.LCM (@IntegerLCM.LCM_step _ 2) 1:/# E
  /three_moduli /IntegerLCM.lcm_pair /= G. smt().
qed.

lemma bounded_reconstruction x y :
  0<=x<60 => 0<=y<60 =>
  x %% 4=y %% 4 => x %% 6=y %% 6 => x %% 5=y %% 5 => x=y.
proof.
move=> Hx Hy H4 H6 H5.
have H : eqm (LCM three_moduli 3) x y.
+ rewrite /AuxResults.LCM -IntegerLCM.LCM_congruence /three_moduli. smt().
move: H. rewrite moduli_with_field !modz_small //.
qed.
