(* Small FFA model: B=4, two limbs, q=13, p=127, M(0)=2, t1=4, t2=5.
   Words and limb arrays are actual pairs; every clone obligation is proved. *)
require import AllCore IntDiv StdOrder.
require FFA_Instance.
import Ring.IntID IntOrder.

op bit_get (a : bool*bool) i = if i=0 then a.`1 else if i=1 then a.`2 else false.
op bit_init (f : int -> bool) = (f 0,f 1).
op pair_get ['a] (a : 'a*'a) i = if i=0 then a.`1 else if i=1 then a.`2 else witness.
op pair_init ['a] (f : int -> 'a) = (f 0,f 1).

clone FFA_Instance.Model as Concrete with
  op FFA.q <- 13,
  op FFA.BN.wsize <- 2,
  op FFA.BN.nlimbs <- 2,
  type FFA.BN.Word.t <- bool*bool,
  op FFA.BN.Word."_.[_]" <- bit_get,
  op FFA.BN.Word.init <- bit_init,
  type 'a FFA.BN.A.t <- ('a*'a),
  op FFA.BN.A."_.[_]" ['a] <- pair_get<:'a>,
  op FFA.BN.A.init ['a] <- pair_init<:'a>
  proof *.

realize FFA.BN.gt0_wsize. proof. trivial. qed.
realize FFA.BN.gt0_nlimbs. proof. trivial. qed.
realize FFA.BN.Word.gt0_size. proof. trivial. qed.
realize FFA.BN.Word.Alphabet.enum_spec.
proof. move=> b. case b; simplify; trivial. qed.
realize FFA.BN.Word.get_out.
proof. move=> a i. rewrite /bit_get. smt(). qed.
realize FFA.BN.Word.initE.
proof. move=> f i. rewrite /bit_get /bit_init /=. smt(). qed.
realize FFA.BN.Word.ext_eq.
proof.
move=> a b H. have H0 := H 0 _; first trivial.
have H1 := H 1 _; first trivial.
move: H0 H1. rewrite /bit_get /=. smt().
qed.
realize FFA.BN.A.get_out.
proof. move=> a i. rewrite /pair_get. smt(). qed.
realize FFA.BN.A.initE.
proof. move=> f i. rewrite /pair_get /pair_init /=. smt(). qed.
realize FFA.BN.A.ext_eq.
proof.
move=> a b H. have H0 := H 0 _; first trivial.
have H1 := H 1 _; first trivial.
move: H0 H1. rewrite /pair_get /=. smt().
qed.

(* Restore the inherited opaque definition equations by unfolding their bodies. *)
realize FFA.BN.Word.setE. proof. by rewrite /Concrete.FFA.BN.Word."_.[_<-_]". qed.
realize FFA.BN.Word.bits2wE. proof. by rewrite /Concrete.FFA.BN.Word.bits2w. qed.
realize FFA.BN.Word.w2bitsE. proof. by rewrite /Concrete.FFA.BN.Word.w2bits. qed.
realize FFA.BN.Word.mapE. proof. by rewrite /Concrete.FFA.BN.Word.map. qed.
realize FFA.BN.Word.map2E. proof. by rewrite /Concrete.FFA.BN.Word.map2. qed.
realize FFA.BN.Word.fillE. proof. by rewrite /Concrete.FFA.BN.Word.fill. qed.
realize FFA.BN.Word.of_intE. proof. by rewrite /Concrete.FFA.BN.Word.of_int. qed.
realize FFA.BN.Word.to_uintE. proof. by rewrite /Concrete.FFA.BN.Word.to_uint. qed.
realize FFA.BN.Word.to_sintE. proof. by rewrite /Concrete.FFA.BN.Word.to_sint. qed.
realize FFA.BN.Word.all_wordsE. proof. by rewrite /Concrete.FFA.BN.Word.all_words. qed.
realize FFA.BN.Word.oneE. proof. by rewrite /Concrete.FFA.BN.Word.onew. qed.
realize FFA.BN.Word.xorE. proof. by rewrite /Concrete.FFA.BN.Word.(+^). qed.
realize FFA.BN.Word.andE. proof. by rewrite /Concrete.FFA.BN.Word.andw. qed.
realize FFA.BN.Word.invE. proof. by rewrite /Concrete.FFA.BN.Word.invw. qed.
realize FFA.BN.Word.orE. proof. by rewrite /Concrete.FFA.BN.Word.orw. qed.
realize FFA.BN.Word.addE. proof. by rewrite /Concrete.FFA.BN.Word.(+). qed.
realize FFA.BN.Word.oppE. proof. by rewrite /Concrete.FFA.BN.Word.([-]). qed.
realize FFA.BN.Word.mulE. proof. by rewrite /Concrete.FFA.BN.Word.( * ). qed.
realize FFA.BN.Word.udivE. proof. by rewrite /Concrete.FFA.BN.Word.(\udiv). qed.
realize FFA.BN.Word.umodE. proof. by rewrite /Concrete.FFA.BN.Word.(\umod). qed.
realize FFA.BN.Word.sdivE. proof. by rewrite /Concrete.FFA.BN.Word.(\sdiv). qed.
realize FFA.BN.Word.smodE. proof. by rewrite /Concrete.FFA.BN.Word.(\smod). qed.
realize FFA.BN.Word.uleE. proof. by rewrite /Concrete.FFA.BN.Word.(\ule). qed.
realize FFA.BN.Word.ultE. proof. by rewrite /Concrete.FFA.BN.Word.(\ult). qed.
realize FFA.BN.Word.sleE. proof. by rewrite /Concrete.FFA.BN.Word.(\sle). qed.
realize FFA.BN.Word.sltE. proof. by rewrite /Concrete.FFA.BN.Word.(\slt). qed.
realize FFA.BN.Word.subcE. proof. by rewrite /Concrete.FFA.BN.Word.subc. qed.
realize FFA.BN.Word.addcE. proof. by rewrite /Concrete.FFA.BN.Word.addc. qed.
realize FFA.BN.Word.muluE. proof. by rewrite /Concrete.FFA.BN.Word.mulu. qed.
realize FFA.BN.Word.wlsrE. proof. by rewrite /Concrete.FFA.BN.Word.(`>>>`). qed.
realize FFA.BN.Word.wlslE. proof. by rewrite /Concrete.FFA.BN.Word.(`<<<`). qed.
realize FFA.BN.Word.sarE. proof. by rewrite /Concrete.FFA.BN.Word.sar. qed.
realize FFA.BN.Word.rorE. proof. by rewrite /Concrete.FFA.BN.Word.ror. qed.
realize FFA.BN.Word.rolE. proof. by rewrite /Concrete.FFA.BN.Word.rol. qed.
realize FFA.BN.A.setE. proof. by rewrite /Concrete.FFA.BN.A."_.[_<-_]". qed.
realize FFA.BN.A.createE. proof. by rewrite /Concrete.FFA.BN.A.create. qed.
realize FFA.BN.A.mapE. proof. by rewrite /Concrete.FFA.BN.A.map. qed.
realize FFA.BN.A.map2E. proof. by rewrite /Concrete.FFA.BN.A.map2. qed.
realize FFA.BN.A.fillE. proof. by rewrite /Concrete.FFA.BN.A.fill. qed.

import Concrete.FFA Concrete.FFA.BN.
import StdBigop.Bigint StdBigop.Bigint.BIA.

lemma base_four : B=4.
proof. by rewrite /B /=. qed.

lemma sigma_two (f : int -> int) : sigma f=f 0+f 1.
proof.
rewrite /sigma (@big_int_recr 1 0) 1:/# /=.
rewrite (@big_int_recr 0 0) 1:/# big_geq //=.
qed.

lemma parameter_values :
  K_min = -1 /\ K_max=8 /\ L_min 2 16 = -10 /\ L_max 2=8 /\
  AuxLB 2 (-1) (-10) 16 32 = -64 /\ AuxUB 2 (-1) (-10)=37.
proof.
rewrite /K_min /K_max /L_min /L_max /AuxLB /AuxUB
  base_four !sigma_two /= /K_min base_four !sigma_two /=. trivial.
qed.

lemma combined_modulus :
  AuxResults.LCM (fun i => if i=1 then 127 else 2) 2=254.
proof.
rewrite /AuxResults.LCM (@IntegerLCM.LCM_step _ 1) 1:/#
  IntegerLCM.LCM_single /IntegerLCM.lcm_pair /=
  -(gcd_modr 2 127) /=. smt().
qed.

(* These are exactly the native and auxiliary equations, with range bounds. *)
type limbs = (bool*bool)*(bool*bool).

op accepts (x y z : limbs) (u v : int) =
  0<=u<16 /\ 0<=v<32 /\
  NativeLHS (-1) u x y z %% 127=0 /\
  AuxLHS 2 v (-1) (-10) u x y z %% 127=0.

lemma concrete_sound x y z u v :
  accepts x y z u v => bn x * bn y %% 13 = bn z %% 13.
proof.
move=> Hacc.
have [Klo [Khi [Llo [Lhi [LB UB]]]]] := parameter_values.
have H := Concrete.FFA_soundness.multiplication_soundness
  (fun _ => 2) (fun _ => v) 1 127 (u-1) 4 5 x y z.
move: H.
rewrite /U Klo Khi /= Llo LB UB combined_modulus base_four
  !sigma_two /= !sigma_two /=.
smt().
qed.

lemma concrete_complete x y z :
  bn x * bn y %% 13 = bn z %% 13 => exists u v, accepts x y z u v.
proof.
move=> Hmul.
have [Klo [Khi [Llo [Lhi [LB UB]]]]] := parameter_values.
have H := Concrete.FFA_completeness.multiplication_completeness
  (fun _ => 2) 1 127 4 5 x y z.
move: H.
rewrite /U Klo Khi /= Llo Lhi LB UB combined_modulus base_four
  !sigma_two /= !sigma_two /=.
move=> H.
have [k [Hk [Hn Ha]]] := H Hmul.
have [v [Hv He]] := Ha 0 _; first trivial.
exists (k+1) v. by rewrite /accepts; smt().
qed.

lemma concrete_iff x y z :
  (exists u v, accepts x y z u v) <=> bn x * bn y %% 13 = bn z %% 13.
proof. smt(concrete_sound concrete_complete). qed.

(* Primality is proved separately; the generic integer theorems need only q>0. *)
lemma prime_by_trial_division p r :
  1<p => 0<=r => p<(r+1)*(r+1) =>
  (forall d, 2<=d<=r => !(d %| p)) => prime p.
proof.
move=> Hp Hr Hsquare Htrial. split=> // d Hd.
have [k E] : exists k, p=k*d by apply/dvdzP.
have Ep : p = `|k| * `|d|.
+ rewrite -normrM -E ger0_norm; smt().
have Hk : 0<=`|k| by smt().
have Hd0 : 0<=`|d| by smt().
have Hdivd : `|d| %| p by rewrite dvdz_norml.
have Hdivk : `|k| %| p.
+ apply dvdzP. exists `|d|. smt().
case (`|d|=1 \/ `|d|=p)=> // Hnontrivial.
have Hboth : 2<=`|d| /\ 2<=`|k| by smt().
have Hsmall : `|d|<=r \/ `|k|<=r.
+ case (`|d|<=r \/ `|k|<=r)=> // Hlarge.
  have Hprod : (r+1)*(r+1)<=`|k|*`|d| by apply ler_pmul; smt().
  smt().
smt().
qed.

lemma foreign_prime : prime 13.
proof.
apply (prime_by_trial_division 13 3); try trivial.
move=> d Hd. have H : d=2 \/ d=3 by smt().
case: H=> ->; by rewrite dvdzE /=.
qed.

lemma native_prime : prime 127.
proof.
apply (prime_by_trial_division 127 11); try trivial.
move=> d Hd.
have H : d=2 \/ d=3 \/ d=4 \/ d=5 \/ d=6 \/ d=7 \/ d=8 \/ d=9 \/ d=10 \/ d=11 by smt().
case: H=> [->|[->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]]; by rewrite dvdzE /=.
qed.

lemma encoding_value n : bn (bn_ofint n)=n %% 16.
proof. by rewrite bn_ofintK /bn_modulus /=. qed.

lemma encoding_digit n i : 0<=i<2 =>
  Word.to_uint (pair_get (bn_ofint n) i)=(n %/ 4^i) %% 4.
proof. move=> Hi. by rewrite bn_ofintE // Word.of_uintK /=. qed.

lemma all_residues_represented n : 0<=n<13 => bn (bn_ofint n)=n.
proof. move=> Hn. rewrite encoding_value modz_small; smt(). qed.

lemma encoded_iff a b c : 0<=a<16 => 0<=b<16 => 0<=c<16 =>
  (exists u v, accepts (bn_ofint a) (bn_ofint b) (bn_ofint c) u v)
  <=> a*b %% 13=c %% 13.
proof.
move=> Ha Hb Hc. rewrite concrete_iff !encoding_value
  (@modz_small a 16) 1:/# (@modz_small b 16) 1:/# (@modz_small c 16) 1:/#.
trivial.
qed.

(* Without this additional range premise the output is only determined modulo q. *)
lemma canonical_output x y z u v :
  0<=bn z<13 => accepts x y z u v => bn z=bn x*bn y %% 13.
proof.
move=> Hz Ha. have H := concrete_sound _ _ _ _ _ Ha.
move: H. rewrite (@modz_small (bn z) 13) 1:/#. smt().
qed.
