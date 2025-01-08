require import AllCore Int IntDiv List StdOrder Bool.
require import BitEncoding StdBigop Bigalg.
(*---*) import Ring.IntID IntOrder BS2Int.
(*---*) import Bigint BIA.

(* from Jasmin require import JWord JUtils JArray JWord_array. *)

require import JWord JUtils JArray JWord_array.

(** TO BE MOVED ELSEWHERE... *)

lemma lex_lt x1 x2 m y1 y2:
 0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
 (y1*m + x1 < y2*m + x2) = (y1 < y2 \/ y1=y2 /\ x1 < x2)
by smt().
(*proof. by move=> /> *; rewrite (divzU (y1 * m + x1) m y1 x1) /#. qed.*)

lemma lex_le x1 x2 m y1 y2:
 0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
 (y1*m + x1 <= y2*m + x2) = (y1 < y2 \/ y1=y2 /\ x1 <= x2)
by smt().
(*proof. by move=> /> *; rewrite (divzU (y1 * m + x1) m y1 x1) /#. qed.*)

lemma lex_eq x1 x2 m y1 y2:
 0 < m => 0 <= x1 < m => 0 <= x2 < m => 0 <= y1 => 0 <= y2 =>
 (y1*m + x1 = y2*m + x2) = (y1 = y2 /\ x1 = x2)
by smt().

lemma modz_pow (a b d: int):
 0 <= b => a ^ b %% d = (a %% d) ^ b %% d.
proof.
elim/natind: b.
 by move => n *; rewrite (_:n=0) 1:/# !expr0.
move=> n Hn IH H.
rewrite !exprS 1..2://.
 rewrite eq_sym -modzMmr -IH.
by done.
rewrite
  1:  modzMmr modzMml //.
qed.

abstract theory BN.


(* Words *)
op wsize : int.
axiom gt0_wsize: 0 < wsize.
clone import BitWord as Word with
  op size <- wsize.
  (* proof gt0_size by apply gt0_wsize. *)
(* import W64.  *)

(** Number of limbs *)
op nlimbs : int.
axiom gt0_nlimbs: 0 < nlimbs.
clone export PolyArray as A with
  op size <- nlimbs
  proof ge0_size by (apply ltrW; apply gt0_nlimbs).

(* BigInt view of an array... *)
type t = Word.t A.t.

op bn_modulus : int = Word.modulus ^ nlimbs.
lemma bn_modulusE: bn_modulus = Word.modulus ^ nlimbs by rewrite /bn_modulus.


(* digits *)
op dig (x: t) (i:int): int = to_uint x.[i]*Word.modulus^i.
lemma digE (x: t) (i:int): dig x i = to_uint x.[i]*Word.modulus^i by rewrite /dig.
hint simplify digE.

(* BigInt value for a prefix of an array *)
op bnk (k:int) (x:t): int = bigi predT (dig x) 0 k.
abbrev [-printing] bn (x:t): int = bnk nlimbs x.

lemma bnkN k x: k <= 0 => bnk k x = 0.
proof. by move => ?; rewrite /bnk big_geq. qed.

lemma bnk0 x: bnk 0 x = 0.
proof. by rewrite bnkN. qed.

lemma bnkS k x: 0 <= k => bnk (k+1) x = dig x k + bnk k x.
proof. 
case: (k=0) => E.
 by rewrite E /= /bnk rangeS range_geq 1:// big_cons /#.
move=> ?; rewrite /bnk (range_cat k) // 1:/# big_cat rangeS addzC; congr.
by rewrite big_cons big_nil /#.
qed.

lemma bnk1 x: bnk 1 x = dig x 0.
proof. by rewrite -(add0z 1) bnkS 1:/# digE expr0 bnk0. qed.

require import StdOrder.
lemma bnk_cmp k x: 0 <= bnk k x < Word.modulus^k.
proof.
case: (k <= 0).
 by move=> *; rewrite bnkN // expr_gt0.
elim/natind: k => // k Hk IH H.
rewrite bnkS // exprS // digE. 
case: (k=0) => E.
  rewrite E bnk0 !expr0 !mulr1 !addr0.
  move: to_uint_cmp; smt().
  (* ??? falha com "smt(to_uint_cmp)." ??? *)
move: (IH _); first smt().
move=> /> ??; split; first smt(@IntOrder to_uint_cmp).
move=> H2; rewrite ltzE -addzA.
apply (lez_trans (to_uint x.[k] * Word.modulus ^ k + Word.modulus^k)).
 smt().
rewrite (_:to_uint x.[k] * Word.modulus ^ k + Word.modulus ^ k=(to_uint x.[k]+1)*Word.modulus^k) 1:/#.
rewrite ler_pmul2r 1:/# -ltzE.
by move: (to_uint_cmp x.[k]) => /#.
qed.

lemma bnk_ltb k x y b:
 0 <= k =>
 bnk (k+1) x < bnk (k+1) y + b2i b
 = (to_uint x.[k] < to_uint y.[k] \/ x.[k]=y.[k] /\ bnk k x < bnk k y + b2i b).
proof.
move=> ?; rewrite !bnkS // !digE.
move: (to_uint_cmp x.[k]) (to_uint_cmp y.[k]) =>  *.
case: b => E; rewrite ?b2i1 ?b2i0 => *.
 rewrite !ltzS lex_le ?expr_gt0 //; move: bnk_cmp to_uint_eq; smt().
by rewrite /= lex_lt ?expr_gt0 //; move: bnk_cmp to_uint_eq; smt().
qed.

lemma bnk_setO k (x: t) i y:
 0 <= k <= i < nlimbs =>
 bnk k x.[i <- y] = bnk k x.
proof.
elim/natind: k => /=.
 by move=> k *; rewrite (_:k=0) 1:/# !bnk0.
by move=> k Hk IH H; rewrite !bnkS // !digE !get_setE 1:/# IH /#.
qed.

(* upper part of a bigint (useful in decreasing loops...) *)

op bnkup k (x: t): int =
 bigi predT (fun i => to_uint x.[i] * Word.modulus^(i-k)) k nlimbs.

lemma bnkup0 x: bnkup 0 x = bn x by done.

lemma bnkup_nlimbs x: bnkup nlimbs x = 0.
proof. by rewrite /bnkup range_geq 1:// big_nil. qed.

lemma bnkupP k x:
 0 < k <= nlimbs =>
 bnkup (k-1) x = to_uint x.[k-1] + bnkup (k) x * Word.modulus.
proof.
move=> *; rewrite /bnkup (range_cat k) 1..2:/# big_cat.
rewrite rangeS big_cons big_nil /predT /=; congr => //.
rewrite mulr_suml; apply eq_big_int => i * /=.
rewrite mulzA; congr.
by rewrite (_:i-(k-1)=i-k+1) 1:/# exprS /#.
qed.

lemma bnkup_setO k (x: t) y:
 0 < k <= nlimbs =>
 bnkup k x.[k - 1 <- y] = bnkup k x.
proof.
move=> H; apply eq_big_seq => x0; rewrite mem_range => * /=.
by rewrite get_setE 1:/# (_:x0 <> k - 1) 1:/#.
qed.

lemma bn_k_kup k x:
 0 <= k <= nlimbs =>
 bn x = bnk k x + bnkup k x * Word.modulus^k.
proof.
elim/natind: k=> [k Hk H|k Hk IH H].
 by rewrite (_:k=0) 1:/# bnk0 bnkup0 expr0.
rewrite bnkS 1:// exprS 1:/# IH 1:/#.
move: (bnkupP (k+1) x _); first smt().
by move=> /= ->; ring.
qed.

lemma bn_mod k x:
 0 <= k <= nlimbs =>
 bn x %% Word.modulus^k = bnk k x.
proof.
by move=> H; rewrite (bn_k_kup k x _) 1:/# modzMDr modz_small; move:bnk_cmp; smt().
qed.

lemma bn_div_kup k x:
 0 <= k <= nlimbs =>
 bn x %/ Word.modulus^k = bnkup k x.
proof.
move=> H; rewrite (bn_k_kup k x _) 1:/# divzMDr; first smt(expr_gt0).
rewrite divz_small; move: bnk_cmp; smt().
qed.

lemma bn_inj x y:
 bn x = bn y => x = y.
proof.
move=> E.
have HH: forall k, 0 <= k <= nlimbs => bnk k x = bnk k y.
 by move=> k Hk; rewrite -!(bn_mod k) 1..2:/# E.
apply A.ext_eq => k Hk; rewrite to_uint_eq.
move: (HH (k+1) _); first smt(). 
rewrite !bnkS 1..2:/# !digE (HH k _) 1:/# => /addIz.
move: (mulIf (Word.modulus ^ k) _); first smt(expr_gt0).
by move => I /I.
qed.

(* BigNum of an integer *)

op bn_ofint x = A.init (fun i => Word.of_int (x %/ Word.modulus^i)).

lemma bn_ofintE x i:
 0 <= i < nlimbs =>
 (bn_ofint x).[i] = Word.of_int (x %/ Word.modulus^i).
proof. by move=> Hi; rewrite /bn_ofint initiE 1:/#. qed.

lemma bnk_ofintK x k:
 0 <= k <= nlimbs =>
 bnk k (bn_ofint x) = x %% Word.modulus ^ k.
proof.
elim/natind: k x.
 move=> k Hk0 x Hk.
 by rewrite (_:k=0) 1:/# bnk0 expr0 modz1.
move=> k Hk0 IH /= x Hk.
case: (k=0) => [->/=|Ek].
 rewrite bnk1 digE expr0 bn_ofintE; first smt(gt0_nlimbs).
 by rewrite expr0 divz1 Word.of_uintK.
rewrite bnkS 1:/# /= IH 1:/# bn_ofintE 1:/# of_uintK.
rewrite exprS 1:/#.
have ->: x %/ Word.modulus ^ k %% Word.modulus 
         = (x %% Word.modulus ^ (k+1)) %/ Word.modulus ^ k.
 rewrite -divz_mod_mul /=; first 2 smt(StdOrder.IntOrder.expr_gt0).
 rewrite exprS; smt(StdOrder.IntOrder.expr_gt0).
have ->: x %% Word.modulus ^ k = (x %% Word.modulus ^ (k+1)) %% Word.modulus ^ k.
 by rewrite modz_dvd_pow 1:/#.
by rewrite /= -divz_eq exprS /#.
qed.

lemma bn_ofintK x:
 bn (bn_ofint x) = x %% bn_modulus.
proof. by rewrite bnk_ofintK /bn_modulus; smt(gt0_nlimbs). qed.

lemma bnK x:
 bn_ofint (bn x) = x.
proof.
apply bn_inj.
rewrite bnk_ofintK; first smt(gt0_nlimbs).
rewrite modz_small; move: bnk_cmp; smt().
qed.

(* to prove by simplification... *)
op bn_seq (x: Word.t list) : int = foldr (fun w r => Word.to_uint w + Word.modulus * r) 0 x.

lemma bn2seq x:
 bn x = bn_seq (to_list x).
proof.
have ->: bn x = bigi predT (fun i => to_uint (nth Word.zero (to_list x) i) * Word.modulus ^ i) 0 (size (to_list x)).
 rewrite size_to_list; apply eq_big_seq => y; rewrite mem_range => /> *; congr.
 rewrite -get_to_list; congr.
 by rewrite !nth_mkseq.
elim: (to_list x) => //=.
 by rewrite /bn_seq big1_eq.
move=> y ys IH; rewrite /bn_seq /= -/(bn_seq ys).
rewrite (range_cat 1) //; first smt(size_ge0).
rewrite big_cat rangeS big_cons big_nil /predT /=; congr.
rewrite -(add0z 1) big_addn /= -IH.
rewrite big_distrr // 1:/#.
apply eq_big_seq => z; rewrite mem_range => /> *.
by rewrite (_:! z+1=0) 1:/# /= exprS // /#.
qed.



end BN.
