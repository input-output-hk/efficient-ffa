(* -------------------------------------------------------------------- *)
require import AllCore FinType IntDiv SmtMap List.
require import StdOrder BitEncoding Bool Distr.
(*---*) import Ring.IntID IntOrder BS2Int.
require import JUtils JArray.

(* -------------------------------------------------------------------- *)
(* Generic word theory used by the limb arithmetic proofs. *)
abstract theory BitWord.

op size : {int | 0 < size} as gt0_size.

clone FinType as Alphabet with
  type t    <- bool,
  op   enum <- [true; false],
  op   card <- 2.

clone include MonoArray with
  type elem <- bool,
  op dfl <- false,
  op size <- size
  rename "of_list"  as "bits2w"
         "to_list"  as "w2bits"
         "^tP$"     as "wordP"
         "sub"      as "bits"
  proof ge0_size by (apply ltzW; apply gt0_size).

(* -------------------------------------------------------------------- *)
abbrev modulus = 2 ^ size.

abbrev max_uint = modulus - 1.
lemma max_uintS: max_uint + 1 = modulus by done.

abbrev min_sint = - 2 ^ (size - 1).
abbrev max_sint =  2 ^ (size - 1) - 1.

lemma ge2_modulus : 2 <= modulus.
proof. rewrite powS_minus ?gt0_size; smt (gt0_size expr_gt0). qed.

lemma gt0_modulus : 0 < modulus.
proof. smt (ge2_modulus). qed.

lemma ge0_modulus : 0 <= modulus.
proof. smt (ge2_modulus). qed.

lemma max_size : max 0 size = size.
proof. by rewrite /max gt0_size. qed.

hint exact : ge0_size gt0_size gt0_modulus ge2_modulus ge0_modulus max_size.

(* --------------------------------------------------------------------- *)
(* Conversions with int                                                  *)

op of_int (x:int) : t =
  bits2w (int2bs size (x %% modulus))
axiomatized by of_intE.

op to_uint (w:t) =
  bs2int (w2bits w)
axiomatized by to_uintE.

op smod (i:int) =
  if 2^(size - 1) <= i then i - modulus
  else i.

op to_sint (w:t) : int = smod (to_uint w)
axiomatized by to_sintE.

abbrev zero = of_int 0.
abbrev one  = of_int 1.

lemma to_uint_cmp (x : t) : 0 <= to_uint x < modulus.
proof.
  by rewrite to_uintE bs2int_ge0 -(size_w2bits x) bs2int_le2Xs.
qed.

lemma to_sint_cmp (x : t) : min_sint <= to_sint x <= max_sint.
proof.
 by rewrite /to_sint /= /smod /=; smt.
qed.

lemma of_uintK (x : int) : to_uint (of_int x) = x %% modulus.
proof.
  by rewrite to_uintE of_intE bits2wK 1:size_int2bs // int2bsK // modz_cmp.
qed.

lemma to_uintK : cancel to_uint of_int.
proof.
  move=> w; rewrite to_uintE of_intE.
  rewrite modz_small.
  + by rewrite bs2int_ge0 ger0_norm // -(size_w2bits w) bs2int_le2Xs.
  by rewrite -(size_w2bits w) bs2intK w2bitsK.
qed.

lemma to_uintK' (x: t) : of_int (to_uint x) = x.
proof. by apply to_uintK. qed.

(*hint simplify of_uintK@1. *)
hint simplify to_uintK'@0.

lemma of_sintK (x:int) :
   to_sint (of_int x) = smod (x %% modulus).
proof. by rewrite to_sintE of_uintK. qed.

lemma to_uint_mod (x : t) : to_uint x %% modulus = to_uint x.
proof. by rewrite modz_small // ger0_norm // to_uint_cmp. qed.

lemma of_int_mod (x : int) : of_int (x %% modulus) = of_int x.
proof. by apply/(can_inj _ _ to_uintK); rewrite !of_uintK modz_mod. qed.

lemma of_int_mod_red (x:int): !(0 <= x < modulus) => of_int x = of_int (x %% modulus).
proof. by rewrite of_int_mod. qed.

hint simplify of_int_mod_red.

lemma to_uint_small i : 0 <= i < modulus => to_uint (of_int i) = i.
proof. by move=> h; rewrite of_uintK modz_small;solve. qed.

lemma to_uint0 : to_uint (of_int 0) = 0 by rewrite of_uintK.
lemma to_uint1 : to_uint (of_int 1) = 1 by rewrite to_uint_small; smt (ge2_modulus).

hint simplify (to_uint0, to_uint1)@0.
hint simplify to_uint_small@1.

lemma word_modeqP (x y : t) :
  to_uint x %% modulus = to_uint y %% modulus => x = y.
proof.
move=> eq_mod; rewrite -(to_uintK x) -(to_uint_mod x).
by rewrite eq_mod to_uint_mod.
qed.

lemma to_uint_eq (x y:t) :  (x = y) <=> (to_uint x = to_uint y).
proof. by rewrite Core.inj_eq // (Core.can_inj _ _  to_uintK). qed.

(* -------------------------------------------------------------------- *)
(* Uniform distribution over word                                       *)
op all_words = map of_int (iota_ 0 modulus)
axiomatized by all_wordsE.

lemma all_wordsP x : x \in all_words.
proof. 
  rewrite all_wordsE mapP; exists (to_uint x).
  by rewrite mema_iota /= to_uint_cmp.
qed.

op dword = duniform all_words.

lemma dword_ll : is_lossless dword.
proof.
apply: duniform_ll; apply/negP=> eq0.
by have := all_wordsP witness; rewrite eq0.
qed.

lemma dword_uni : is_uniform dword.
proof. by apply duniform_uni. qed.

lemma dword_fu : is_full dword.
proof. by apply /duniform_fu/all_wordsP. qed.

lemma dword_funi : is_funiform dword.
proof. apply is_full_funiform;[apply dword_fu| apply dword_uni]. qed.

hint exact random : dword_ll dword_fu dword_funi.

(* -------------------------------------------------------------------- *)
op int_bit x i = (x%%modulus) %/ 2 ^ i %% 2 <> 0.

lemma of_intwE x i :
   (of_int x).[i] = (0 <= i < size /\ int_bit x i).
proof.
  rewrite of_intE; case (0 <= i < size) => /= hi; last by rewrite get_out.
  by rewrite get_bits2w // nth_mkseq.
qed.

lemma zerowE i: zero.[i] = false.
proof. by rewrite of_intwE /int_bit. qed.
hint simplify zerowE.

lemma of_int_powm1 p i :
  0 <= p =>
  (of_int (2^p - 1)).[i] = (0 <= i < size /\ i < p).
proof.
  case: (0 <= i < size) => [[h0i his] /= hp | hi]; last by rewrite get_out.
  have aux : forall p, 0 <= p <= size => (of_int (2 ^ p - 1)).[i] = (true /\ i < p).
  + move=> {p hp} p hp.
    rewrite of_intwE 1:// /int_bit /= (modz_small (2 ^ p - 1)).
    + smt (gt0_pow2 ler_weexpn2l).
    case (i < p) => hip /=.
    + have -> : p = ((p - i - 1) + 1) + i by ring.
      rewrite h0i his exprD_nneg // 1:/# divzMDl; 1: smt (gt0_pow2).
      by rewrite exprD_nneg 1:/# //= modzMDl divNz // gt0_pow2.
    by rewrite divz_small //; smt (gt0_pow2 ler_weexpn2l).
  case : (p <= size) => hps; 1: by apply aux.
  rewrite (_:i < p) 1:/# -of_int_mod.
  have -> : p = (p-size) + size by ring.
  rewrite exprD_nneg 1:/# 1://.
  by rewrite modzMDl -(modzMDl 1 (-1) modulus) /= of_int_mod aux 1:// his.
qed.

lemma get_to_uint w i : w.[i] = (0 <= i < size /\ to_uint w %/ 2 ^ i %% 2 <> 0).
proof.
  case : (0 <= i < size) => hi;last by rewrite get_out.
  rewrite -{1}(to_uintK w) of_intwE hi /int_bit (modz_small _ modulus) 2://.
  by apply bound_abs; apply to_uint_cmp.
qed.

lemma b2i_get w i : 0 <= i => b2i w.[i] = to_uint w %/ 2 ^ i %% 2.
proof.
  move=> hi;rewrite get_to_uint hi.
  case (i < size) => his //=; 1: smt (modz_cmp).
  rewrite divz_small //; apply bound_abs.
  smt (to_uint_cmp ler_weexpn2l ge0_size).
qed.

lemma bits_divmod w i j: 0 <= i => 0 <= j => bs2int (bits w i j) = ((to_uint w) %/ 2^i) %% 2^j.
proof.
  move => hi; rewrite /bits.
  elim /intind: j.
  + by rewrite mkseq0 bs2int_nil /=.
  move=> j hj hrec; rewrite mkseqS 1:// bs2int_rcons.
  rewrite size_mkseq ler_maxr 1:// /= hrec.
  have {2}->:= modz_pow_split (i+j+1) (i+j) (to_uint w) 2 _; 1: smt().
  have hij1 : 2 ^ (i + j + 1) = 2^(j+1) * 2^i.
  + by rewrite -exprD_nneg 1:/# 1://;congr;ring.
  have hij : 2 ^ (i + j) = 2^j * 2^i.
  + by rewrite -exprD_nneg 1:/# 1://;congr;ring.
  have h2i0 : 2 ^ i <> 0 by smt (gt0_pow2).
  rewrite -addzA {2}hij1 -mulzA divzMDl 1://.
  rewrite {2}hij -mulzA divzMDl 1://.
  rewrite modzMDl !modz_pow2_div; 1,2:smt().
  have -> : i + j + 1 - (i + j) = 1 by ring.
  have -> : i + j - i = j by ring.
  rewrite (exprD_nneg 2 j 1) 1,2:// pow2_1 (modz_small _ (2^j * 2)).
  + apply bound_abs; split => [|?]; 1: smt (modz_cmp to_uint_cmp gt0_pow2).
    by rewrite -hrec; smt (modz_cmp to_uint_cmp gt0_pow2).
  by rewrite addzC mulzC b2i_get 1:/#.
qed.

lemma bitsE w k len : bits w k len = mkseq (fun (i:int) => w.[k+i]) len.
proof. done. qed.

lemma to_uintRL (w:t) (x:int) : to_uint w = x %% 2^size => w = of_int x.
proof.
  by move=> h;rewrite -of_int_mod; apply: (canRL _ _ _ _ to_uintK).
qed.

lemma to_uint_bits w : to_uint w = bs2int (bits w 0 size).
proof. by rewrite to_uintE /w2bits /bits /=. qed.

(* -------------------------------------------------------------------- *)
op zerow = zero.

op onew  = of_int (modulus - 1)
axiomatized by oneE.

op (+^) : t -> t -> t = map2 (^^)
axiomatized by xorE.

op andw : t -> t -> t = map2 (/\)
axiomatized by andE.

op oppw (w : t): t = w.

op invw : t -> t = map ([!])
axiomatized by invE.

op orw : t -> t -> t = map2 (\/)
axiomatized by orE.

(* -------------------------------------------------------------------- *)

lemma zerowiE i: zerow.[i] = false.
proof. apply zerowE. qed.

lemma onewE i: onew.[i] = (0 <= i < size).
proof.
  rewrite oneE; case (0 <= i < size) => hi; 2:by rewrite get_out.
  by rewrite of_int_powm1 //= 1:/# hi.
qed.

lemma xorwE w1 w2 i: (w1 +^ w2).[i] = w1.[i] ^^ w2.[i].
proof.
  by rewrite xorE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma andwE (w1 w2:t) i: (andw w1 w2).[i] = (w1.[i] /\ w2.[i]).
proof.
  by rewrite andE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma orwE (w1 w2:t) i: (orw w1 w2).[i] = (w1.[i] \/ w2.[i]).
proof.
  by rewrite orE; case (0 <= i < size) => hi;[ rewrite map2iE | rewrite !get_out].
qed.

lemma invwE (w:t) i:
  (invw w).[i] = (0 <= i < size /\ !w.[i]).
proof. by rewrite invE mapE initE;case (0 <= i < _). qed.

lemma oppwE (w:t) i: (oppw w).[i] = w.[i].
proof. by []. qed.

hint rewrite bwordE : zerowE zerowiE onewE xorwE andwE invwE.
hint simplify (zerowE, zerowiE, onewE, xorwE, andwE, invwE, orwE).

(* -------------------------------------------------------------------- *)
lemma onew_neq0: onew <> zerow.
proof.
  apply/negP=> /wordP/(_ 0) /=.
  by rewrite negb_imply neqF.
qed.

lemma xorw0: right_id zero (+^).
proof. by move=> w; apply/wordP=> i _. qed.

lemma xorwA: associative (+^).
proof. by move=> w1 w2 w3; apply/wordP=> i _; rewrite !bwordE xorA. qed.

lemma xorwC: commutative (+^).
proof. by move=> w1 w2; apply/wordP=> i _; rewrite !bwordE xorC. qed.

lemma xorwK: forall x, x +^ x = zero.
proof. by move=> w; apply/wordP=> i _; rewrite !bwordE. qed.

lemma andw1: right_id onew andw.
proof. by move=> w; apply/wordP=> i h; rewrite !bwordE h. qed.

lemma andwA: associative andw.
proof. by move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE andbA. qed.

lemma andwC: commutative andw.
proof. by move=> w1 w2; apply/wordP=> i h; rewrite !bwordE andbC. qed.

lemma andwDl: left_distributive andw (+^).
proof. move=> w1 w2 w3; apply/wordP=> i h; rewrite !bwordE /#. qed.

lemma andwK: idempotent andw.
proof. by move=> x; apply/wordP=> i h; rewrite !bwordE andbb. qed.

(* -------------------------------------------------------------------- *)
instance bring with t
  op rzero = zerow
  op rone  = onew
  op add   = (+^)
  op mul   = andw
  op opp   = oppw

  proof oner_neq0 by apply/onew_neq0
  proof addr0     by apply/xorw0
  proof addrA     by (move=> w1 w2 w3; rewrite xorwA)
  proof addrC     by apply/xorwC
  proof addrK     by apply/xorwK
  proof mulr1     by apply andw1
  proof mulrA     by (move=> w1 w2 w3; rewrite andwA)
  proof mulrC     by apply/andwC
  proof mulrDl    by apply/andwDl
  proof mulrK     by apply/andwK
  proof oppr_id   by trivial.

pred unitw (w:t) = w = onew.
op iandw (w:t) = if w = onew then onew else w.

clone Ring.ComRing as WRing with
   type t <- t,
   op zeror <- zero,
   op ( + ) <- (+^),
   op [ - ] <- oppw,
   op oner  <- onew,
   op ( * ) <- andw,
   op invr  <- iandw,
   pred unit <- unitw
proof *.
realize addrA.     proof. apply xorwA. qed.
realize addrC.     proof. apply xorwC. qed.
realize add0r.     proof. move=> ?;ring. qed.
realize addNr.     proof. move=> ?;ring. qed.
realize oner_neq0. proof. apply onew_neq0. qed.
realize mulrA.     proof. apply andwA. qed.
realize mulrC.     proof. apply andwC. qed.
realize mul1r.     proof. move=> ?;ring. qed.
realize mulrDl.    proof. apply andwDl. qed.
realize mulVr.     proof. move=> ?;rewrite /unitw /iandw => -> /=;ring. qed.
realize unitout.   proof. by move=> x;rewrite /unitw /iandw => ->. qed.

realize unitP.
proof.
move=> x y; rewrite /unitw !wordP => + i Hi -/(_ i Hi).
by rewrite andwE onewE Hi /#.
qed.

lemma xor0w w : of_int 0 +^ w = w.
proof. by apply WRing.add0r. qed.

lemma xorw0_s w : w +^ of_int 0 = w.
proof. by apply WRing.addr0. qed.

lemma xorw1 w : w +^ onew = invw w.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma xor1w w : onew +^ w = invw w.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma and0w w : andw (of_int 0) w = of_int 0.
proof. by apply WRing.mul0r. qed.

lemma andw0 w : andw w (of_int 0) = of_int 0.
proof. by apply WRing.mulr0. qed.

lemma and1w w : andw onew w = w.
proof. by apply WRing.mul1r. qed.

lemma andw1_s w : andw w onew = w.
proof. by apply WRing.mulr1. qed.

lemma orw0 w : orw w zero = w.
proof. by apply wordP => i hi. qed.

lemma or0w w : orw zero w = w.
proof. by apply wordP => i hi. qed.

lemma orw1 w : orw w onew = onew.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma or1w w : orw onew w = onew.
proof. by apply wordP => i hi /=; case (0 <= i < size). qed.

lemma orwK w : orw w w = w.
proof. by apply wordP => i hi /=; case (w.[i]). qed.

lemma xorwK_s w1 w2 : w1 = w2 => (w1 +^ w2) = zero.
proof. move=> ->;apply xorwK. qed.

lemma andwK_s w1 w2 : w1 = w2 => andw w1 w2 = w1.
proof. move=> ->;apply andwK. qed.

lemma orwK_s w1 w2 : w1 = w2 => orw w1 w2 = w1.
proof. move=> ->;apply orwK. qed.

lemma andw_invw w: andw w (invw w) = zerow.
proof. by rewrite -xorw1; ring. qed.

lemma orw_xorw w1 w2: orw w1 w2 = w1 +^ w2 +^ (andw w1 w2).
proof.
apply wordP => i Hi.
rewrite orE !xorE andE !map2iE //.
by case: w1.[i]; case: w2.[i].
qed.

lemma andw_orwDl: left_distributive andw orw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma andw_orwDr: right_distributive andw orw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma orw_andwDl: left_distributive orw andw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma orw_andwDr: right_distributive orw andw.
proof.
by move=> x y z; rewrite !orw_xorw; ring.
qed.

lemma orwC x y: orw x y = orw y x.
proof. by rewrite orw_xorw andwC (xorwC x) -orw_xorw. qed.

lemma xorw_invw w: w +^ (invw w) = onew.
proof.
apply wordP => i Hi.
rewrite xorE !map2iE // onewE invwE !Hi /=.
by case: w.[i].
qed.

lemma orw_invw w: orw w (invw w) = onew.
proof. by rewrite orw_xorw andw_invw -xorwA xorw0_s xorw_invw. qed.

hint simplify (xor0w, xorw0_s, xorw1, xor1w,
               and0w, andw0, and1w, andw1_s,
               or0w, orw0, orw1, or1w,
               xorwK_s, andwK_s, orwK_s).

(* --------------------------------------------------------------------- *)
(* Arimethic operations                                                  *)

op ulift1 (f : int -> int) (w : t) =
  of_int (f (to_uint w)).

op ulift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_uint w1) (to_uint w2)).

op slift2 (f : int -> int -> int) (w1 w2 : t) =
  of_int (f (to_uint w1) (to_uint w2)).

op ( + ) = ulift2 Int.( + ) axiomatized by addE.
op ([-]) = ulift1 Int.([-]) axiomatized by oppE.
op ( * ) = ulift2 Int.( * ) axiomatized by mulE.

op (\udiv) = ulift2 IntDiv.( %/) axiomatized by udivE.
op (\umod) = ulift2 IntDiv.( %%) axiomatized by umodE.

(* TODO check this *)
op (\sdiv) = slift2 IntDiv.( %/) axiomatized by sdivE.
op (\smod) = slift2 IntDiv.( %%) axiomatized by smodE.

(* --------------------------------------------------------------------- *)
(* Comparisons                                                           *)

op (\ule) (x y : t) = (to_uint x) <= (to_uint y) axiomatized by uleE.
op (\ult) (x y : t) = (to_uint x) <  (to_uint y) axiomatized by ultE.

op (\sle) (x y : t) = (to_sint x) <= (to_sint y) axiomatized by sleE.
op (\slt) (x y : t) = (to_sint x) <  (to_sint y) axiomatized by sltE.

lemma ult_of_int x y :
   (of_int x \ult of_int y) = (x %% modulus < y %% modulus).
proof. by rewrite ultE /= !of_uintK. qed.

lemma ule_of_int x y :
   (of_int x \ule of_int y) = (x %% modulus <= y %% modulus).
proof. by rewrite uleE /= !of_uintK. qed.

lemma uleNgt x y : x \ule y <=> ! y \ult x.
proof. by rewrite ultE uleE lerNgt. qed.

lemma ultNge x y: x \ult y <=> ! y \ule x.
proof. by rewrite ultE uleE ltzNge. qed.

lemma ult_of_int_true x y :
   (x %% modulus < y %% modulus) => (of_int x \ult of_int y) = true.
proof. by rewrite ult_of_int => ->. qed.

lemma ult_of_int_false x y :
   !(x %% modulus < y %% modulus) => (of_int x \ult of_int y) = false.
proof. by rewrite ult_of_int => ->. qed.

lemma ule_of_int_true x y :
   (x %% modulus <= y %% modulus) => (of_int x \ule of_int y) = true.
proof. by rewrite ule_of_int => ->. qed.

lemma ule_of_int_false x y :
   !(x %% modulus <= y %% modulus) => (of_int x \ule of_int y) = false.
proof. by rewrite ule_of_int => ->. qed.

hint simplify (ult_of_int_true, ult_of_int_false, ule_of_int_true, ule_of_int_false).

(* --------------------------------------------------------------------- *)
(* ComRing                                                               *)

op is_inverse (w wi: t) = wi * w = of_int 1.
op unit (w:t) = exists wi, is_inverse w wi.
op invr (w:t) = Logic.choiceb (is_inverse w) w.

lemma of_intN (x : int) : of_int (-x) = - of_int x.
proof.
rewrite oppE /ulift1 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod modzNm.
qed.

lemma to_uintN (x : t) : to_uint (-x) = (- to_uint x) %% modulus.
proof. by rewrite oppE /ulift1 of_uintK. qed.

lemma of_intD (x y : int) : of_int (x + y) = of_int x + of_int y.
proof.
rewrite addE /ulift2 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod !(modzDml, modzDmr).
qed.

lemma to_uintD (x y : t) : to_uint (x + y) = (to_uint x + to_uint y) %% modulus.
proof. by rewrite addE /ulift2 of_uintK. qed.

lemma of_intM (x y : int) : of_int x * of_int y = of_int (x * y).
proof.
rewrite mulE /ulift2 /=; apply/word_modeqP=> /=.
by rewrite !of_uintK !modz_mod !(modzMml, modzMmr).
qed.

lemma to_uintM (x y : t) : to_uint (x * y) = (to_uint x * to_uint y) %% modulus.
proof. by rewrite mulE /ulift2 !of_uintK. qed.

lemma to_uintD_small (x y : t) : to_uint x + to_uint y < modulus =>
  to_uint (x + y) = to_uint x + to_uint y.
proof.
  move=> h;rewrite to_uintD modz_small 2://; smt (to_uint_cmp).
qed.

lemma to_uintM_small (x y : t) : to_uint x * to_uint y < modulus =>
  to_uint (x * y) = (to_uint x * to_uint y).
proof.
  move=> h;rewrite to_uintM modz_small 2://; smt (to_uint_cmp).
qed.

clone export Ring.ComRing as WRingA with
   type t <- t,
   op zeror <- of_int 0,
   op ( + ) <- BitWord.( + ),
   op [ - ] <- BitWord.([-]),
   op oner  <- of_int 1,
   op ( * ) <- BitWord.( * ),
   op invr  <- invr,
   pred unit  <- BitWord.unit proof *.

realize addrA.
proof.
  move=> x y z; rewrite addE /ulift2 !to_uintD -of_int_mod modzDmr.
  by rewrite -(of_int_mod (_ + to_uint z)) modzDml addrA.
qed.

realize addrC.
proof. by move=> x y; rewrite !addE /ulift2 addzC. qed.

realize add0r.
proof. by move=> x; rewrite addE /ulift2; cbv delta. qed.

realize addNr.
proof.
  move=> x; rewrite addE oppE /ulift2 /ulift1 of_uintK.
  by rewrite -of_int_mod modzDml addNz.
qed.

realize oner_neq0.
proof.
  apply /negP => heq.
  have := of_uintK 1; rewrite heq of_uintK mod0z.
  rewrite modz_small //;smt (ge2_modulus).
qed.

realize mulrA.
 move=> x y z; rewrite mulE /ulift2 !to_uintM -of_int_mod modzMmr.
  by rewrite -(of_int_mod (_ * to_uint z)) modzMml mulrA.
qed.

realize mulrC.
proof. by move=> x y; rewrite !mulE /ulift2 mulzC. qed.

realize mul1r.
proof. by move=> x; rewrite mulE /ulift2 to_uint1. qed.

realize mulrDl.
proof.
  move=> x y z; rewrite !addE !mulE /ulift2.
  rewrite !of_uintK -of_int_mod modzMml eq_sym.
  by rewrite -of_int_mod modzDml modzDmr mulrDl.
qed.

realize mulVr.
proof. by move=> x /choicebP /= ->. qed.

realize unitP.
proof. by move=> w wi hinv;exists wi. qed.

realize unitout.
proof. by move=> x /negb_exists /=; apply choiceb_dfl. qed.

abbrev (^) = WRingA.exp.

lemma ofintS (n : int) : 0 <= n => of_int (n + 1) = of_int 1 + of_int n.
proof. by rewrite of_intD addrC. qed.

lemma to_uintB (x y: t) : y \ule x => to_uint (x - y) = to_uint x - to_uint y.
proof.
  rewrite uleE=> hle.
  rewrite to_uintD to_uintN modzDmr modz_small //; smt (to_uint_cmp).
qed.

(* Add simplification rule for rewriting *)
(* FIXME add direction for hint simplify *)
lemma of_intN' (x : int) : - of_int x = of_int (-x).
proof. by rewrite of_intN. qed.

lemma of_intS (x y : int) : of_int (x - y) = of_int x - of_int y.
proof. by rewrite of_intD of_intN. qed.

lemma of_intS' (x y : int) : of_int x - of_int y = of_int (x - y).
proof. by rewrite of_intS. qed.

lemma of_intD' (x y : int) : of_int x + of_int y = of_int (x + y).
proof. by rewrite of_intD. qed.

lemma of_intM' (x y : int) : of_int x * of_int y = of_int (x * y).
proof. by rewrite of_intM. qed.

hint simplify (of_intS', of_intM')@0.
hint simplify (of_intD')@1.

lemma addr0_s w : w + of_int 0 = w.
proof. by apply addr0. qed.

lemma add0r_s w : of_int 0 + w = w.
proof. by apply add0r. qed.

lemma mulr1_s w : w * of_int 1 = w.
proof. by apply mulr1. qed.

lemma mul1r_s w : of_int 1 * w = w.
proof. by apply mul1r. qed.

lemma mulr0_s w : w * of_int 0 = of_int 0.
proof. by apply mulr0. qed.

lemma mul0r_s w : of_int 0 * w = of_int 0.
proof. by apply mul0r. qed.

lemma addA_ofint w i j : w + of_int i + of_int j = w + of_int (i + j).
proof. by rewrite -addrA. qed.

lemma addS_ofint w i j : w + of_int i - of_int j = w + of_int (i - j).
proof. by rewrite -addrA -of_intS. qed.

hint simplify (addr0_s, add0r_s, mul1r_s, mulr1_s, mul0r_s, mulr0_s, addA_ofint).



(* --------------------------------------------------------------------- *)
(* Ring tactic                                                           *)

op zerow_ring = of_int 0.
op onew_ring  = of_int 1.

instance ring with t
  op rzero = BitWord.zerow_ring
  op rone  = BitWord.onew_ring
  op add   = BitWord.( + )
  op opp   = BitWord.([-])
  op mul   = BitWord.( * )
  op expr  = WRingA.exp
  op ofint = BitWord.of_int

  proof oner_neq0 by apply oner_neq0
  proof addr0     by apply addr0
  proof addrA     by apply addrA
  proof addrC     by apply addrC
  proof addrN     by apply addrN
  proof mulr1     by apply mulr1
  proof mulrA     by apply mulrA
  proof mulrC     by apply mulrC
  proof mulrDl    by apply mulrDl
  proof expr0     by apply expr0
  proof exprS     by apply exprS
  proof ofint0    by done
  proof ofint1    by done
  proof ofintS    by apply ofintS
  proof ofintN    by apply of_intN.

(* --------------------------------------------------------------------- *)
(* Exact arithmetic operations                                           *)
(*
op subc : t -> t -> bool -> bool * t.
op addc : t -> t -> bool -> bool * t.
op mulu : t -> t -> t * t.
*)

op borrow_sub x y b = to_uint x < to_uint y + b2i b.

op subc (x y:t) (b: bool): bool * t = (borrow_sub x y b, x-(y+of_int (b2i b)))
 axiomatized by subcE.

lemma subcP x y c:
 let (c',z) = subc x y c
 in to_uint z - modulus * b2i c' = to_uint x - (to_uint y + b2i c).
proof.
rewrite subcE /borrow_sub /=.
case: (to_uint y + b2i c = modulus) => H.
 rewrite to_uintD.
 have -> /=: to_uint (- (y + of_int (b2i c))) = 0.
  rewrite to_uintN to_uintD of_uintK (modz_small (b2i c)).
   by apply bound_abs; smt(ge2_modulus).
  by rewrite H modzz /=.
 rewrite H modz_small.
  by apply bound_abs; apply to_uint_cmp.
 have ->: to_uint x < modulus by smt(to_uint_cmp).
 smt().
case: (to_uint x < to_uint y + b2i c) => ?/=.
 have E: to_uint y + b2i c = to_uint (y + of_int (b2i c)).
  rewrite to_uintD_small.
   rewrite !of_uintK modz_small; first by  apply bound_abs; smt(ge2_modulus).
   by case: c => /=?; smt(to_uint_cmp).
  by rewrite of_uintK modz_small //; apply bound_abs; smt(ge2_modulus).
 rewrite E b2i1 /= eqr_sub.
 have ->: x - (y + of_int (b2i c)) = -((y + of_int (b2i c)) - x) by ring.
 rewrite to_uintN -modzDl modz_small.
  have ?: 0 < to_uint (y + of_int (b2i c) - x) <= `|modulus|.
   rewrite to_uintB; first by rewrite uleE -E; smt().
   rewrite -E; smt(to_uint_cmp).
  smt(to_uint_cmp).
 rewrite to_uintB; first by rewrite uleE -E; smt().
 smt(to_uint_cmp).
rewrite b2i0 /= to_uintB.
 rewrite uleE to_uintD_small.
  by rewrite of_uintK modz_small; smt(to_uint_cmp ge2_modulus).
 rewrite of_uintK modz_small; first smt(ge2_modulus).
 smt(ge2_modulus to_uint_cmp).
by rewrite to_uintD of_uintK !modz_small; smt(ge2_modulus to_uint_cmp).
qed.

abbrev subc_borrow x y c = (subc x y c).`1.

op carry_add x y c = modulus <= to_uint x + to_uint y + b2i c.

lemma carry_addC x y c: carry_add x y c = carry_add y x c.
proof. by rewrite /carry_add (addzC (to_uint x)). qed.

op addc (x y: t) (c: bool) : bool * t = (carry_add x y c, x+y+of_int (b2i c))
 axiomatized by addcE.

lemma addcP x y c:
 let (c',z) = addc x y c
 in to_uint z + modulus * b2i c' = to_uint x + to_uint y + b2i c.
proof.
rewrite addcE !addE /ulift2 /= !of_uintK /= modzDmr modzDml /carry_add.
have /= ?: to_uint x + to_uint y + b2i c < 2*modulus.
 by move: (to_uint_cmp x) (to_uint_cmp y); smt().
case: (modulus <= to_uint x + to_uint y + b2i c) => /= ?.
 have {1}->: to_uint x + to_uint y + b2i c = to_uint x + to_uint y + b2i c - modulus + modulus
  by ring.
 rewrite b2i1 modzDr modz_small.
  by apply bound_abs; smt(to_uint_cmp bound_abs).
 by ring.
by rewrite modz_small; smt(to_uint_cmp bound_abs).
qed.

abbrev addc_carry x y c = (addc x y c).`1.

op mulhi (x y: t) : t =
 of_int ((to_uint x * to_uint y) %/ modulus).

lemma mulhiP (x y: t):
 to_uint (x*y) + modulus * to_uint (mulhi x y) = to_uint x * to_uint y.
proof.
have [??] := (to_uint_cmp x).
have [??] := (to_uint_cmp y).
rewrite to_uintM to_uint_small.
 apply divz_cmp; first smt().
 split; first smt().
 by move=> _; apply ltr_pmul.
by rewrite {3}(divz_eq (to_uint x * to_uint y) modulus) /#.
qed.

lemma mulhi0 (x y: t):
 to_uint x* to_uint y < modulus => to_uint (mulhi x y) = 0.
proof.
move=> ?; rewrite /mulhi divz_small //; apply bound_abs.
split=> //; smt (to_uint_cmp).
qed.

op mulu (x y: t): t * t = (mulhi x y, x*y) axiomatized by muluE.

(* --------------------------------------------------------------------- *)
(* Bitwize operations                                                    *)

abbrev (`&`) = andw.
abbrev (`|`) = orw.
abbrev (`^`) = (+^).

op msb (b: t): bool = 2^(size - 1) <= (to_uint b).

op lsb (w: t): bool = w.[0].

op (`>>>`) (x : t) (i : int) =
  init (fun j => x.[j + i])
axiomatized by wlsrE.

op (`<<<`) (x : t) (i : int) =
  init (fun j => x.[j - i])
axiomatized by wlslE.

op sar (x:t) (i:int) =
  init (fun j => x.[min (size- 1) (j + i)])
axiomatized by sarE.

lemma shlwE w k i : (w `<<<` k).[i] = (0 <= i < size && w.[i - k]).
proof. by rewrite wlslE initE. qed.

lemma shrwE w k i : (w `>>>` k).[i] = (0 <= i < size && w.[i + k]).
proof. by rewrite wlsrE initE. qed.
hint simplify (shrwE, shlwE).

lemma int_bitMP i j k : 0 <= k => 0 <= j < size =>
  int_bit (i * 2 ^ k) j = (0 <= j - k < size /\ int_bit i (j - k)).
proof.
  move=> hk [h0j hjs];rewrite /int_bit modz_pow2_div 1:/# modz_dvd.
  + by have /= := dvdz_exp2l 2 1; apply => /#.
  case: (0 <= j - k < size) => [ [hjk1 hjk2] | hjk]  /=;last first.
  + have hlt : (j < k) by smt().
    have ->: k = (k-j-1) + 1 + j by ring.
    rewrite exprD_nneg 1:/# 1:// -mulzA mulzK; 1: smt (gt0_pow2).
    by rewrite exprD_nneg 1:/# //= -mulzA modzMl.
  rewrite (modz_pow2_div size) 1:/# modz_dvd.
  + by have /= := dvdz_exp2l 2 1; apply => /#.
  have {1}-> : j = (j - k) + k by ring.
  by rewrite exprD_nneg 1,2:// divzMpr 1:gt0_pow2.
qed.

lemma int_bitDP i j k : 0 <= i < modulus => 0 <= k => 0 <= j < size =>
  int_bit (i %/ 2 ^ k) j = (0 <= j + k < size /\ int_bit i (j + k)).
proof.
  move=> hi hk [h0j hjs];rewrite /int_bit.
  rewrite !(modz_small _ modulus); 1,2: apply bound_abs; 2:done.
  + by apply divz_cmp; [apply gt0_pow2 | smt (gt0_pow2)].
  case: (0 <= j + k < size) => hjk.
  + have {1}->:= divz_eq i (2^(j+k)).
    have {1}->:= divz_eq (i %% 2 ^ (j + k)) (2^k).
    pose id := i %/ 2 ^ (j + k). pose im := i %% 2 ^ (j + k).
    have -> : id * 2 ^ (j + k) + (im %/ 2 ^ k * 2 ^ k + im %% 2 ^ k) =
           (id * 2^j + im %/ 2 ^ k) * 2^k + im %% 2 ^ k.
    + by rewrite exprD_nneg 1,2://;ring.
    rewrite divzMDl. smt (gt0_pow2).
    rewrite (divz_small (im %% 2 ^ k) (2 ^ k)).
    + apply bound_abs;apply modz_cmp;apply gt0_pow2.
    rewrite /= divzMDl. smt (gt0_pow2).
    rewrite (divz_small (im %/ 2 ^ k) (2 ^ j)) 2://.
    apply bound_abs; apply divz_cmp; 1:by apply gt0_pow2.
    by rewrite -exprD_nneg 1,2://;apply modz_cmp;apply gt0_pow2.
  rewrite /= (divz_small (i %/ 2 ^ k) (2 ^ j)) 2://.
  apply bound_abs;apply divz_cmp; 1: by apply gt0_pow2.
  rewrite -exprD_nneg 1,2://;smt (ler_weexpn2l).
qed.

lemma shlMP i k : 0 <= k => (of_int i `<<<` k) = of_int (i * 2^k).
proof.
  by move=> hk;apply wordP => j hj; rewrite shlwE !of_intwE hj /= -int_bitMP.
qed.

lemma shrDP i k : 0 <= k => (of_int i `>>>` k) = of_int (i %% modulus %/ 2^k).
proof.
  move=> hk;rewrite -(of_int_mod i).
  apply wordP => j hj; rewrite shrwE !of_intwE hj /= -int_bitDP //.
  by apply modz_cmp.
qed.

lemma to_uint_shl (w:t) i :
  0 <= i => to_uint (w `<<<` i) = (to_uint w * 2^ i) %% modulus.
proof.
  by move=> hi; rewrite -{1}(to_uintK w) shlMP 1:// of_uintK.
qed.

lemma to_uint_shr (w:t) i :
  0 <= i => to_uint (w `>>>` i) = to_uint w %/ 2^ i.
proof.
  move=> hi;rewrite -{1}(to_uintK w) shrDP 1:// of_uintK.
  rewrite (modz_small (to_uint w)).
  + by apply bound_abs; apply to_uint_cmp.
  rewrite modz_small 2://.
  apply bound_abs; apply divz_cmp; [apply gt0_pow2 | ].
  smt (to_uint_cmp gt0_pow2).
qed.

lemma shrw_shlw w i : w `>>>` i = w `<<<` (-i).
proof. by apply wordP => k hk /=. qed.

lemma shrw_add w i j : 0 <= i => 0 <= j => w `>>>` i `>>>` j = w `>>>` (i + j).
proof.
  move=> hi hj; apply wordP => k hk /=;rewrite hk /=.
  case : (0 <= k + j < size) => hkj /=; 1:congr;ring.
  by rewrite get_out 1:/#.
qed.

lemma shrw_out w i : size <= i => w `>>>` i = zero.
proof.
  by move=> hi;apply wordP => k hk/=; rewrite get_out 1:/#.
qed.
hint simplify (shrw_add, shrw_out).

lemma shlw_add w i j : 0 <= i => 0 <= j => w `<<<` i `<<<` j = w `<<<` (i + j).
proof.
  move=> hi hj; apply wordP => k hk /=;rewrite hk /=.
  case : (0 <= k - j < size) => hkj /=; 1:congr;ring.
  by rewrite get_out 1:/#.
qed.

lemma shlw_out w i : size <= i => w `<<<` i = zero.
proof.
  by move=> hi;apply wordP => k hk/=; rewrite get_out 1:/#.
qed.
hint simplify (shlw_add, shlw_out).

lemma shrw_map2 f w1 w2 i : f false false = false =>
   (map2 f) (w1 `>>>` i) (w2 `>>>` i) = (map2 f w1 w2) `>>>` i.
proof.
  move=> hf;apply wordP => k hk.
  rewrite map2iE // !shrwE hk.
  case: (0 <= k + i < size) => hki; 1: by rewrite map2iE.
  by rewrite !get_out.
qed.

lemma shlw_map2 f w1 w2 i : f false false = false =>
   (map2 f) (w1 `<<<` i) (w2 `<<<` i) = (map2 f w1 w2) `<<<` i.
proof.
  move=> hf;apply wordP => k hk.
  rewrite map2iE // !shlwE hk.
  case: (0 <= k - i < size) => hki; 1: by rewrite map2iE.
  by rewrite !get_out.
qed.

lemma shrw_and w1 w2 i : (w1 `>>>` i) `&` (w2 `>>>` i) = (w1 `&` w2) `>>>` i.
proof. by rewrite andE shrw_map2. qed.

lemma shrw_xor w1 w2 i : (w1 `>>>` i) `^` (w2 `>>>` i) = (w1 `^` w2) `>>>` i.
proof. by rewrite xorE shrw_map2. qed.

lemma shrw_or w1 w2 i : (w1 `>>>` i) `|` (w2 `>>>` i) = (w1 `|` w2) `>>>` i.
proof. by rewrite orE shrw_map2. qed.

lemma shlw_and w1 w2 i : (w1 `<<<` i) `&` (w2 `<<<` i) = (w1 `&` w2) `<<<` i.
proof. by rewrite andE shlw_map2. qed.

lemma shlw_xor w1 w2 i : (w1 `<<<` i) `^` (w2 `<<<` i) = (w1 `^` w2) `<<<` i.
proof. by rewrite xorE shlw_map2. qed.

lemma shlw_or w1 w2 i : (w1 `<<<` i) `|` (w2 `<<<` i) = (w1 `|` w2) `<<<` i.
proof. by rewrite orE shlw_map2. qed.

hint simplify (shrw_and, shrw_xor, shrw_or, shlw_and, shlw_xor, shlw_or).

op ror (x : t) (i : int) =
  init (fun j => x.[(j + i) %% size])
axiomatized by rorE.

op rol (x : t) (i : int) =
  init (fun j => x.[(j - i) %% size])
axiomatized by rolE.

abbrev (`|>>>|`) = ror.
abbrev (`|<<<|`) = rol.

lemma rorwE w k i :
  (w `|>>>|` k).[i] = if (0 <= i < size) then w.[(i+k) %% size] else false.
proof. by rewrite rorE initE. qed.

lemma rolwE w k i :
  (w `|<<<|` k).[i] = if (0 <= i < size) then w.[(i-k) %% size] else false.
proof. by rewrite rolE initE. qed.

hint simplify (rorwE, rolwE).

lemma rol_xor w i : 0 <= i < size =>
  w `|<<<|` i = (w `<<<` i) `^` (w `>>>` (size - i)).
proof.
  move=> hi; apply wordP => k hk /=.
  rewrite hk /=.
  case (0 <= k - i < size) => hki.
  + rewrite modz_small; 1: by apply bound_abs.
    by rewrite (get_out _ (k + (size - i))) 1:/#.
  rewrite modz_sub_carry // 1:/# (get_out _ _ hki) /=.
  by congr;ring.
qed.

lemma rol_xor_simplify w1 w2 i si:
   w1 = w2 => si = size - i => 0 <= i < size =>
   (w1 `<<<` i) `^` (w2 `>>>` si) = w1 `|<<<|` i.
proof. by move=> 2!-> hi;rewrite rol_xor. qed.

(* --------------------------------------------------------------------- *)
(* Like between bitwize operations and arithmetic operations             *)

lemma and_mod k w :
  0 <= k =>
    w `&` of_int (2^k - 1) = of_int (to_uint w %% 2^k).
proof.
  move=> hk;apply wordP => i hi /=.
  rewrite of_int_powm1 1:// of_intwE hi /= /int_bit.
  rewrite (modz_small _ modulus).
  + apply bound_abs; smt (le_modz modz_cmp to_uint_cmp gt0_pow2).
  case (i < k) => hik /=.
  + rewrite modz_pow2_div 1:/# modz_dvd.
    + by have /= := dvdz_exp2l 2 1; apply => /#.
    by rewrite get_to_uint hi.
  rewrite divz_small 2://; smt (gt0_pow2 modz_cmp ler_weexpn2l).
qed.

lemma to_uint_and_mod k w :
  0 <= k =>
    to_uint (w `&` of_int (2^k - 1)) = to_uint w %% 2^k.
proof.
  move=> hk ; rewrite and_mod 1:// of_uintK modz_small //.
  apply bound_abs; smt (le_modz to_uint_cmp gt0_pow2 modz_cmp).
qed.

lemma to_uintNE w:
 to_uint (-w) = (modulus - to_uint w) %% modulus.
proof.
rewrite to_uintN.
by have /= ->:= (modzMDl 1).
qed.

lemma of_intNE (n:int):
  of_int (-n) = of_int (modulus - n).
proof.
rewrite of_intN.
apply word_modeqP; congr.
rewrite to_uintN !of_uintK modzNm.
by have /= ->:= (modzMDl 1).
qed.

lemma of_int_modulus: of_int modulus = BitWord.zero.
proof. rewrite !of_intE modzz modz_small; smt(gt0_modulus). qed.

lemma to_uint_onew: to_uint onew = max_uint.
proof. by rewrite oneE of_uintK modz_small //; smt(ge2_modulus). qed.

lemma onewS: onew + BitWord.one = BitWord.zero.
proof.
apply word_modeqP; congr.
by rewrite to_uintD to_uint0 to_uint_onew to_uint1 max_uintS modzz.
qed.

lemma map2_w2bits_w2bits f w1 w2 : map2 f (w2bits w1) (w2bits w2) = w2bits (map2 f w1  w2).
proof. by rewrite map2_w2bits bits2wK // size_map2 minrE !size_w2bits. qed.

lemma map_w2bits_w2bits f w : map f (w2bits w) = w2bits (map f w).
proof. by rewrite map_w2bits bits2wK 2:// size_map size_w2bits. qed.

lemma to_uintD_disjoint w1 w2:
 w1 `&` w2 = BitWord.zero =>
 to_uint (w1 + w2) = to_uint w1 + to_uint w2.
proof.
move=> H; have H0: to_uint (w1 `&` w2) = 0 by smt(to_uint0).
rewrite to_uintD_small //.
move: H0; rewrite !to_uintE.
rewrite andE => H0.
apply bs2int_add_disjoint; rewrite ?size_w2bits //.
by rewrite -H0 map2_w2bits_w2bits.
qed.

lemma orw_disjoint w1 w2:
 w1 `&` w2 = BitWord.zero => w1 `|` w2 = w1 + w2.
proof.
move=> H; have H0: to_uint (w1 `&` w2) = 0 by smt(to_uint0).
apply word_modeqP; congr.
rewrite to_uintD_disjoint //.
move: H0; rewrite !to_uintE andE => H0.
by rewrite orE -bs2int_or_add ?size_mkseq // 1:-H0 map2_w2bits_w2bits.
qed.

lemma to_uint_orw_disjoint w1 w2:
 w1 `&` w2 = zero =>
 to_uint (w1 `|` w2) = to_uint w1 + to_uint w2.
proof. by move=> *; rewrite orw_disjoint // to_uintD_disjoint. qed.

lemma ule_andN0 (x y: t):
 x `&` invw y = BitWord.zero =>
 x \ule y.
proof.
rewrite andwC => ?; have: to_uint (invw y `&` x) = 0 by smt(to_uint0).
rewrite !to_uintE andE invE => ?.
have ->: x \ule y = (0 <= (to_uint y - to_uint x)) by rewrite uleE /#.
rewrite !to_uintE; apply bs2int_sub_common.
+ by rewrite !size_w2bits. 
by rewrite map_w2bits_w2bits map2_w2bits_w2bits.
qed.

lemma ule_andw x y:
 x `&` y \ule x.
proof.
rewrite andwC; apply ule_andN0.
by rewrite -andwA andw_invw andw0.
qed.

lemma to_uint_ule_andw (x y: t):
 to_uint (x `&` y) <= to_uint x.
proof. have := ule_andw x y; by rewrite uleE. qed.

lemma ule_orw x y:
 x \ule x `|` y.
proof.
have {1}->: x = (x`|`y) `&` (x`|`invw y).
 rewrite -{1}orw0.
 have :=(andw_invw y); rewrite /zerow => <-.
 by rewrite orw_andwDr.
by apply ule_andw.
qed.

lemma subw_xorw w1 w2:
 invw w1 `&` w2 = BitWord.zero => w1 - w2 = w1 `^` w2.
proof.
move=> H; have H0: to_uint (invw w1 `&` w2) = 0 by smt(to_uint0).
apply word_modeqP; congr.
rewrite to_uintB.
 by apply ule_andN0; rewrite andwC.
move: H0; rewrite !to_uintE andE invE => H0.
rewrite xorE.
rewrite -bs2int_xor_sub ?size_mkseq //.
+ by rewrite map_w2bits_w2bits map2_w2bits_w2bits.
by rewrite map2_w2bits_w2bits.
qed.

lemma orw_xpnd w1 w2: w1 `|` w2 = w1 - w1 `&` w2 + w2.
proof.
rewrite subw_xorw.
 by rewrite andwA (andwC (invw w1)) andw_invw and0w.
rewrite -orw_disjoint.
 by rewrite andwDl -andwA andwK xorwK.
rewrite !orw_xorw.
have ->: w1 `^` (w1 `&` w2) `&` w2 = zerow.
 by rewrite andwDl -andwA andwK xorwK.
by rewrite -!xorwA xorw0 (xorwC w2).
qed.

lemma ones_compl w: w + invw w = onew.
proof.
have:= orw_invw w.
rewrite orw_xpnd andw_invw => <-.
by ring.
qed.

lemma twos_compl (x: t):  -x = invw x + BitWord.one.
proof.
apply (addrI x); rewrite addrA ones_compl onewS.
by ring.
qed.

lemma minus_one: -one = onew.
proof.
rewrite twos_compl -orw_disjoint.
 by rewrite andwC andw_invw.
by rewrite orwC orw_invw.
qed.

lemma to_uint_invw w: to_uint (invw w) = max_uint - to_uint w.
proof.
rewrite -to_uint_onew -to_uintB.
 rewrite uleE to_uint_onew.
 smt(to_uint_cmp).
by congr; rewrite -(ones_compl w); ring.
qed.

abbrev masklsb k = of_int (2^(max 0 k) - 1).

lemma masklsbNeg k:
 k <= 0 => masklsb k = zerow.
proof. move=> ?; rewrite ler_maxl //. qed.

lemma masklsbE k i:
 (masklsb k).[i] = 0 <= i < min k size.
proof.
case: (0 <= k) => H; last first.
+ by rewrite ler_maxl 1:/# /=; smt(ge0_size). 
rewrite ler_maxr 1://. 
case: (0 <= i < size) => Hi; last by rewrite get_out /#.
rewrite of_intE.
case: (size <= k) => H0.
+ rewrite powm1_mod // get_bits2w //.
  have /=:= (bs2int_nseq true size); rewrite ge0_size /= => <-.
  have:= bs2intK (nseq size true); rewrite size_nseq ler_maxr 1:/# => ->.
  by rewrite nth_nseq //#. 
rewrite modz_small; first by smt(gt0_pow2 ler_weexpn2l).
rewrite get_bits2w //.
have /= := (bs2int_nseq true k); rewrite H /= => <-.
rewrite (bs2int_pad (size - k)).
pose L:= _++_.
have:= bs2intK L; rewrite size_cat !size_nseq !ler_maxr 1,2:/#.
have -> ->: k + (size-k) = size by smt().
rewrite /L nth_cat size_nseq ler_maxr //=.
by case: (i < k) => ?; rewrite nth_nseq /#.
qed.

hint simplify masklsbE.

lemma shrl_andmaskN k w:
 0 <= k =>
 w `>>>` k `<<<` k = w `&` invw (masklsb k).
proof. by move=> Hk; apply wordP => i Hi /= /#. qed.

lemma shlw_andmask k1 k2 w:
 0 <= k1 <= k2 < size =>
 (w `<<<` k1) `&` masklsb k2 = (w `&` masklsb (k2-k1)) `<<<` k1.
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma andmask_shrw k1 k2 w:
 0 <= k2 < k1 < size =>
 (w `&` masklsb k1) `>>>` k2
 = (w `>>>` k2) `&` masklsb (k1-k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /min /=.
smt(get_out).
qed.

lemma andmask_shlw k1 k2 w:
 0 <= k1 < size =>
 (w `&` masklsb k1) `<<<` k2
 = (w `<<<` k2) `&` masklsb (k1+k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite Hi /= /min.
smt(get_out).
qed.

lemma shrw_shlw_disjoint k1 k2 w1 w2:
 0 <= k1 < size <= k1+k2 =>
 (w1 `>>>` k1) `&` (w2 `<<<` k2) = zero.
proof.
move=> *; apply/wordP => i Hi /=; rewrite Hi /= /min.
smt(get_out).
qed.

lemma andmaskK k w:
 size <= k =>  w `&` masklsb k = w.
proof. by move=> *; apply/wordP => i Hi /= /#. qed.

lemma shrw_andmaskK k1 k2 w:
 0 <= k1 < size <= (k1+k2)%Int =>
 (w `>>>` k1) `&` masklsb k2 = (w `>>>` k1).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma mask_and_mask k1 k2:
 0 <= k1 => 0 <= k2 =>
 (masklsb k1 `&` masklsb k2) = masklsb (min k1 k2).
proof. by move=> *; apply/wordP => i Hi /= /#. qed.

lemma shrw_shlw_shlw k1 k2 x:
 0 <= k1 < k2 =>
 x `>>>` k1 `<<<` k2 = (x `&` invw (masklsb k1)) `<<<` (k2-k1).
proof. by move=> *; apply/wordP => i Hi /= /#. qed.

lemma shrw_shlw_shrw k1 k2 x:
 0 <= k2 <= k1 < size =>
 x `>>>` k1 `<<<` k2 = (x `&` invw (masklsb k1)) `>>>` (k1-k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma shlw_shrw_shlw k1 k2 x:
 0 <= k2 <= k1 < size =>
 x `<<<` k1 `>>>` k2 = (x `&` masklsb (size-k1)) `<<<` (k1-k2).
proof.
move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /min.
smt(get_out).
qed.

lemma shlw_shrw_shrw k1 k2 x:
 0 <= k1 < k2 < size =>
 x `<<<` k1 `>>>` k2 = (x `&` masklsb (size-k1)) `>>>` (k2-k1).
proof. by move=> *; apply/wordP => i Hi /=; rewrite !Hi /= /#. qed.

lemma splitwE k w:
 0 <= k =>
 to_uint w = to_uint (w `&` masklsb k) + 2^k * to_uint (w `>>>` k).
proof.
move=> ?; rewrite to_uint_and_mod ler_maxr // to_uint_shr //.
by rewrite {1}(divz_eq (to_uint w) (2^k)); ring.
qed.

op splitBits k w = (w `&` masklsb k, w `>>>` k).

lemma splitBits_disjoint k w:
 0 <= k =>
 (splitBits k w).`1 `&` ((splitBits k w).`2 `<<<` k) = BitWord.zero.
proof.
move => *; rewrite /splitBits /= shrl_andmaskN //.
by rewrite andwA -(andwA w) (andwC _ w) andwA andwK -andwA andw_invw andw0.
qed.

lemma to_uint_splitBits k w:
 0 <= k =>
 to_uint (splitBits k w).`1 + 2^k * to_uint (splitBits k w).`2 = to_uint w.
proof. by move=> ?; rewrite eq_sym (splitwE k w). qed.

op splitMask mask w = (w `&` mask, w `&` invw mask).

abbrev splitAt k = splitMask (masklsb k).

lemma splitMask_and0 mask w:
 (splitMask mask w).`1 `&` (splitMask mask w).`2 = BitWord.zero.
proof.
rewrite /splitMask /=.
by rewrite (andwC w) -andwA (andwA w) andwK (andwC w) andwA andw_invw and0w.
qed.

lemma splitMask_add mask w:
 (splitMask mask w).`1 + (splitMask mask w).`2 = w.
proof.
rewrite -orw_disjoint; first by apply (splitMask_and0 mask w).
by rewrite /splitMask /= !(andwC w) -andw_orwDl orw_invw and1w.
qed.

lemma splitAtP k w:
 0 <= k <= size =>
 to_uint (splitAt k w).`1 = to_uint w %% 2^k
 /\ to_uint (splitAt k w).`2 = 2^k * (to_uint w %/ 2^k).
proof.
move=> /> *.
rewrite /splitMask /= -shrl_andmaskN //; split.
+ by rewrite to_uint_and_mod ler_maxr.
rewrite to_uint_shl // to_uint_shr // modz_small //; last by smt(to_uint_cmp).
apply bound_abs; split.
+ smt(divr_ge0 divz_ge0 gt0_pow2 to_uint_cmp).
move=> *.
by apply (ler_lt_trans (to_uint w)); smt(leq_trunc_div gt0_pow2 to_uint_cmp).
qed.

op wmulhs (v1 v2: t) = 
  of_int (to_sint v1 * to_sint v2 %/ modulus).

end BitWord.
