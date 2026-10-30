import EfficientFFA.Native.CompleteGates

namespace EfficientFFA.Native.ECEncoding
open EllipticCurve
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

def selectRight (bp bq : ℤ) := (1-bp)*bq
def selectInverse (bp bq zx zy : ℤ) := (1-bp)*(1-bq)*zx*zy
def selectDouble (bp bq zx zy : ℤ) := (1-bp)*(1-bq)*zx*(1-zy)
def selectAdd (bp bq zx : ℤ) := (1-bp)*(1-bq)*(1-zx)

/-- The activations are polynomial expressions, not unconstrained witness bits. -/
theorem selectors_partition (bp bq zx zy : ℤ) :
    bp + selectRight bp bq + selectInverse bp bq zx zy +
      selectDouble bp bq zx zy + selectAdd bp bq zx = 1 := by
  unfold selectRight selectInverse selectDouble selectAdd
  ring

def FlagCopy (s a b : ℤ) := s*(a-b) ≡ 0 [ZMOD E.params.p]

@[simp] theorem flagCopy_zero (a b : ℤ) : E.FlagCopy 0 a b := by simp [FlagCopy]

theorem flagCopy_one_iff {a b : ℤ} (ha : E.NativeBit a) (hb : E.NativeBit b) :
    E.FlagCopy 1 a b ↔ a = b := by
  constructor
  · intro h
    have hm : a ≡ b [ZMOD E.params.p] := by
      simpa only [FlagCopy, one_mul, Int.modEq_iff_dvd, zero_sub, neg_sub] using h
    simpa only [Int.ModEq, Int.emod_eq_of_lt ha.1 ha.2.1,
      Int.emod_eq_of_lt hb.1 hb.2.1] using hm
  · rintro rfl
    simp [FlagCopy]

def taggedP (x : CompleteWires n) (bp : ℤ) : Encoded (ZMod q) := ⟨E.wireP x, decide (bp=1)⟩
def taggedQ (x : CompleteWires n) (bq : ℤ) : Encoded (ZMod q) := ⟨E.wireQ x, decide (bq=1)⟩
def taggedR (x : CompleteWires n) (br : ℤ) : Encoded (ZMod q) := ⟨E.wireR x, decide (br=1)⟩

/-- One conjunction of native congruences over one shared limb assignment.
Input/output flags and the two zero selectors are prover-supplied native wires.
Branch activations are fixed polynomial expressions in those checked bits. -/
structure CompleteCore (x : CompleteWires n) (bp bq br zx zy : ℤ) : Prop where
  bounded : E.WiresBounded x
  p_bit : E.NativeBit bp
  q_bit : E.NativeBit bq
  r_bit : E.NativeBit br
  negative_q : E.NegGate (x 9) (x 3) 1
  x_test : E.ZeroTest (x 0) (x 2) (x 7) zx
  y_test : E.ZeroTest (x 1) (x 9) (x 8) zy

structure CompleteConstraints (x : CompleteWires n) (bp bq br zx zy : ℤ) : Prop
    extends E.CompleteCore x bp bq br zx zy where
  left_x : E.CopyLimbs bp (x 4) (x 2)
  left_y : E.CopyLimbs bp (x 5) (x 3)
  left_flag : E.FlagCopy bp br bq
  right_x : E.CopyLimbs (selectRight bp bq) (x 4) (x 0)
  right_y : E.CopyLimbs (selectRight bp bq) (x 5) (x 1)
  right_flag : E.FlagCopy (selectRight bp bq) br bp
  inverse_flag : E.FlagCopy (selectInverse bp bq zx zy) br 1
  double_flag : E.FlagCopy (selectDouble bp bq zx zy) br 0
  add_flag : E.FlagCopy (selectAdd bp bq zx) br 0
  double : E.DoubleGates x (selectDouble bp bq zx zy)
  add : E.AddGates x (selectAdd bp bq zx)

/-- Soundness quantifies over arbitrary raw flags, selectors, shared limbs and
quotient witnesses. No branch choice or selector correctness is assumed. -/
theorem completeConstraints_sound {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    (hfit : E.params.B ≤ E.params.p) {x : CompleteWires n} {bp bq br zx zy : ℤ}
    (hP : C.Valid (E.taggedP x bp)) (hQ : C.Valid (E.taggedQ x bq))
    (hc : E.CompleteConstraints x bp bq br zx zy) :
    C.CompleteAccepts (E.taggedP x bp) (E.taggedQ x bq) (E.taggedR x br) := by
  have hx := hc.bounded
  have hnq := (E.negGate_one_iff (hx 9) (hx 3)).mp hc.negative_q
  rcases E.nativeBit_cases hp hc.p_bit with hbp | hbp
  · subst bp
    rcases E.nativeBit_cases hp hc.q_bit with hbq | hbq
    · subst bq
      rcases (E.zeroTest_iff hp (hx 0) (hx 2) (hx 7) zx).mp hc.x_test with ⟨hzx, hex⟩ | ⟨hzx, hix⟩
      · subst zx
        rcases (E.zeroTest_iff hp (hx 1) (hx 9) (hx 8) zy).mp hc.y_test with ⟨hzy, hey⟩ | ⟨hzy, hiy⟩
        · subst zy
          have hbr : br = 1 := (E.flagCopy_one_iff hc.r_bit E.nativeBit_one).mp
            (by simpa [selectInverse] using hc.inverse_flag)
          exact .inverse (by simp [taggedP]) (by simp [taggedQ]) hex
            (hey.trans hnq) (by simp [taggedR, hbr])
        · subst zy
          have hbr : br = 0 := (E.flagCopy_one_iff hc.r_bit E.nativeBit_zero).mp
            (by simpa [selectDouble] using hc.double_flag)
          have hneq : E.limbValue (x 1) ≠ -E.limbValue (x 3) := by
            intro he
            have hz : E.limbValue (x 1) = E.limbValue (x 9) := he.trans hnq.symm
            simp [hz] at hiy
          have heq : E.wireP x = E.wireQ x := by
            have hpC : C.OnCurve (E.wireP x) := hP (by simp [taggedP])
            have hqC : C.OnCurve (E.wireQ x) := hQ (by simp [taggedQ])
            have hy := (C.same_x_cases hpC hqC hex).resolve_right hneq
            exact congrArg₂ Coordinates.mk hex hy
          apply Curve.CompleteAccepts.double (by simp [taggedP]) (by simp [taggedQ]) heq (E.limbValue (x 6))
          refine ⟨by simp [taggedR, taggedP, hbr], ?_⟩
          intro _
          exact (E.doubleGates_one_iff hx).mp (by simpa [selectDouble] using hc.double)
      · subst zx
        have hneq : (E.wireP x).x ≠ (E.wireQ x).x := by
          intro he
          simp [wireP, wireQ] at he
          simp [he] at hix
        have hbr : br = 0 := (E.flagCopy_one_iff hc.r_bit E.nativeBit_zero).mp
          (by simpa [selectAdd] using hc.add_flag)
        apply Curve.CompleteAccepts.distinct (by simp [taggedP]) (by simp [taggedQ]) hneq (E.limbValue (x 6))
        exact ⟨by simp [taggedR, hbr], (E.addGates_one_iff hx).mp (by simpa [selectAdd] using hc.add)⟩
    · subst bq
      have heX := (E.copyLimbs_one_iff hfit (hx 4) (hx 0)).mp
        (by simpa [selectRight] using hc.right_x)
      have heY := (E.copyLimbs_one_iff hfit (hx 5) (hx 1)).mp
        (by simpa [selectRight] using hc.right_y)
      have hbr : br = 0 := (E.flagCopy_one_iff hc.r_bit hc.p_bit).mp
        (by simpa [selectRight] using hc.right_flag)
      exact .right (by simp [taggedP]) (by simp [taggedQ])
        (by simp [taggedR, taggedP, wireR, wireP, hbr, heX, heY])
  · subst bp
    have heX := (E.copyLimbs_one_iff hfit (hx 4) (hx 2)).mp hc.left_x
    have heY := (E.copyLimbs_one_iff hfit (hx 5) (hx 3)).mp hc.left_y
    have hbr := (E.flagCopy_one_iff hc.r_bit hc.q_bit).mp hc.left_flag
    exact .left (by simp [taggedP])
      (by simp [taggedR, taggedQ, wireR, wireQ, hbr, heX, heY])


@[simp] theorem copyLimbs_refl (s : ℤ) (x : Limbs n) : E.CopyLimbs s x x := by
  intro i
  simp

def zeroBit (a b : ZMod q) : ℤ := if a = b then 1 else 0

def completeValues (P Q R : Encoded (ZMod q)) (slope : ZMod q) : Fin 10 → ZMod q :=
  ![P.coords.x, P.coords.y, Q.coords.x, Q.coords.y, R.coords.x, R.coords.y,
    slope, (P.coords.x-Q.coords.x)⁻¹, (P.coords.y-(-Q.coords.y))⁻¹, -Q.coords.y]

noncomputable def completeWires (P Q R : Encoded (ZMod q)) (slope : ZMod q) : CompleteWires n :=
  fun i => E.canonicalLimbs (completeValues P Q R slope i)

theorem completeWires_bounded (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.WiresBounded (E.completeWires P Q R slope) := fun i => E.canonicalLimbs_bounded (completeValues P Q R slope i)

@[simp] theorem wireP_complete (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.wireP (E.completeWires P Q R slope) = P.coords := by
  simp [wireP, completeWires, completeValues]
@[simp] theorem wireQ_complete (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.wireQ (E.completeWires P Q R slope) = Q.coords := by
  simp [wireQ, completeWires, completeValues]
@[simp] theorem wireR_complete (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.wireR (E.completeWires P Q R slope) = R.coords := by
  simp [wireR, completeWires, completeValues]

@[simp] theorem decode_bitValue (b : Bool) : decide (bitValue b = 1) = b := by
  cases b <;> decide

theorem bitValue_nativeBit (b : Bool) : E.NativeBit (bitValue b) := by
  cases b
  · exact E.nativeBit_zero
  · exact E.nativeBit_one

@[simp] theorem taggedP_complete (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.taggedP (E.completeWires P Q R slope) (bitValue P.infinity) = P := by
  simp [taggedP]
@[simp] theorem taggedQ_complete (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.taggedQ (E.completeWires P Q R slope) (bitValue Q.infinity) = Q := by
  simp [taggedQ]
@[simp] theorem taggedR_complete (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.taggedR (E.completeWires P Q R slope) (bitValue R.infinity) = R := by
  simp [taggedR]

theorem zeroTest_canonical {p : ℕ} [Fact p.Prime] (hp : E.params.p = p) (a b : ZMod q) :
    E.ZeroTest (E.canonicalLimbs a) (E.canonicalLimbs b)
      (E.canonicalLimbs (a-b)⁻¹) (zeroBit a b) := by
  rw [E.zeroTest_iff hp (E.canonicalLimbs_bounded _) (E.canonicalLimbs_bounded _)
    (E.canonicalLimbs_bounded _)]
  simp only [E.limbValue_canonical]
  by_cases he : a = b
  · simp [zeroBit, he]
  · exact Or.inr ⟨by simp [zeroBit, he], mul_inv_cancel₀ (sub_ne_zero.mpr he)⟩

theorem completeCore_canonical {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.CompleteCore (E.completeWires P Q R slope)
      (bitValue P.infinity) (bitValue Q.infinity) (bitValue R.infinity)
      (zeroBit P.coords.x Q.coords.x) (zeroBit P.coords.y (-Q.coords.y)) := by
  refine ⟨E.completeWires_bounded _ _ _ _, E.bitValue_nativeBit _, E.bitValue_nativeBit _,
    E.bitValue_nativeBit _, ?_, ?_, ?_⟩
  · apply (E.negGate_one_iff (E.completeWires_bounded _ _ _ _ 9)
      (E.completeWires_bounded _ _ _ _ 3)).mpr
    simp [completeWires, completeValues]
  · simpa [completeWires, completeValues] using E.zeroTest_canonical hp P.coords.x Q.coords.x
  · simpa [completeWires, completeValues] using E.zeroTest_canonical hp P.coords.y (-Q.coords.y)

theorem addGates_complete_iff (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.AddGates (E.completeWires P Q R slope) 1 ↔ AddChecks P.coords Q.coords R.coords slope := by
  rw [E.addGates_one_iff (E.completeWires_bounded _ _ _ _)]
  simp [completeWires, completeValues]

theorem doubleGates_complete_iff (P Q R : Encoded (ZMod q)) (slope : ZMod q) :
    E.DoubleGates (E.completeWires P Q R slope) 1 ↔ DoubleChecks C P.coords R.coords slope := by
  rw [E.doubleGates_one_iff (E.completeWires_bounded _ _ _ _)]
  simp [completeWires, completeValues]


/-- Completeness constructs one limb assignment for the whole gadget, including
inverse and slope witnesses. Canonical copies agree limb-for-limb. -/
theorem completeConstraints_complete {p : ℕ} [Fact p.Prime] (hnative : E.params.p = p)
    {P Q R : Encoded (ZMod q)} (hP : C.Valid P) (ha : C.CompleteAccepts P Q R) :
    ∃ slope, E.CompleteConstraints (E.completeWires P Q R slope)
      (bitValue P.infinity) (bitValue Q.infinity) (bitValue R.infinity)
      (zeroBit P.coords.x Q.coords.x) (zeroBit P.coords.y (-Q.coords.y)) := by
  cases ha with
  | left hp he =>
    subst R
    refine ⟨0, E.completeCore_canonical hnative P Q Q 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [bitValue, hp, selectRight, selectInverse, selectDouble, selectAdd,
      completeWires, completeValues, CopyLimbs, FlagCopy]
  | right hp hq he =>
    subst R
    refine ⟨0, E.completeCore_canonical hnative P Q P 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [bitValue, hp, hq, selectRight, selectInverse, selectDouble, selectAdd,
      completeWires, completeValues, CopyLimbs, FlagCopy]
  | inverse hp hq hx hy hr =>
    refine ⟨0, E.completeCore_canonical hnative P Q R 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [bitValue, hp, hq, hr, zeroBit, hx, hy, selectRight, selectInverse,
      selectDouble, selectAdd, CopyLimbs, FlagCopy]
  | double hp hq he slope hc =>
    have heq : P = Q := by cases P; cases Q; simp_all
    subst Q
    have hr : R.infinity = false := hc.1.trans hp
    have hd := C.double_den_ne (hP hp) (hc.2 hp)
    have hy : P.coords.y ≠ -P.coords.y := by
      intro he
      apply hd
      linear_combination he
    refine ⟨slope, E.completeCore_canonical hnative P P R slope, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [bitValue, hp, hr, zeroBit, hy, selectRight, selectInverse,
      selectDouble, selectAdd, CopyLimbs, FlagCopy, E.doubleGates_complete_iff, hc.2 hp]
  | distinct hp hq hne slope hc =>
    refine ⟨slope, E.completeCore_canonical hnative P Q R slope, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [bitValue, hp, hq, hc.1, zeroBit, hne, selectRight, selectInverse,
      selectDouble, selectAdd, CopyLimbs, FlagCopy, E.addGates_complete_iff, hc.2]

/-- The external relation of the shared-wire native constraint system.
The equalities below interpret its public wires; branch guards occur only in
CompleteConstraints as native equations, never as acceptance premises. -/
def CompleteCircuit (P Q R : Encoded (ZMod q)) : Prop :=
  ∃ x bp bq br zx zy, E.CompleteConstraints x bp bq br zx zy ∧
    E.taggedP x bp = P ∧ E.taggedQ x bq = Q ∧ E.taggedR x br = R

theorem completeCircuit_iff {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    (hfit : E.params.B ≤ E.params.p) (P Q R : Encoded (ZMod q))
    (hP : C.Valid P) (hQ : C.Valid Q) :
    E.CompleteCircuit P Q R ↔ C.CompleteAccepts P Q R := by
  constructor
  · rintro ⟨x, bp, bq, br, zx, zy, hc, rfl, rfl, rfl⟩
    exact E.completeConstraints_sound hp hfit hP hQ hc
  · intro ha
    obtain ⟨slope, hc⟩ := E.completeConstraints_complete hp hP ha
    exact ⟨_, _, _, _, _, _, hc, E.taggedP_complete _ _ _ _,
      E.taggedQ_complete _ _ _ _, E.taggedR_complete _ _ _ _⟩

theorem completeCircuit_sound {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    (hfit : E.params.B ≤ E.params.p) {P Q R : Encoded (ZMod q)}
    (hP : C.Valid P) (hQ : C.Valid Q) (hc : E.CompleteCircuit P Q R) :
    ∃ hR : C.Valid R, C.decode R hR = C.decode P hP + C.decode Q hQ :=
  C.complete_sound hP hQ ((E.completeCircuit_iff hp hfit P Q R hP hQ).mp hc)

theorem completeCircuit_complete {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    {P Q : Encoded (ZMod q)} (hP : C.Valid P) (hQ : C.Valid Q) :
    ∃ R, E.CompleteCircuit P Q R := by
  obtain ⟨R, ha⟩ := C.complete_exists hP hQ
  obtain ⟨slope, hc⟩ := E.completeConstraints_complete hp hP ha
  exact ⟨R, _, _, _, _, _, _, hc, E.taggedP_complete _ _ _ _,
    E.taggedQ_complete _ _ _ _, E.taggedR_complete _ _ _ _⟩

end EfficientFFA.Native.ECEncoding
