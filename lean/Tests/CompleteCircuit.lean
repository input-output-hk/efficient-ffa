import EfficientFFA

namespace EfficientFFA.Tests.CompleteCircuit
open EfficientFFA.Native EfficientFFA.Native.ECEncoding EllipticCurve
private abbrev E := Instances.Curve17.encoding
private abbrev C := Instances.Curve17.curve
local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩
private theorem hp : E.params.p = (65537 : ℕ) := rfl
private theorem hfit : E.params.B ≤ E.params.p := by decide
private def P : Encoded (ZMod 17) := ⟨⟨5,1⟩,false⟩
private def Q : Encoded (ZMod 17) := ⟨⟨6,3⟩,false⟩
private theorem validP : C.Valid P := by intro _; unfold Curve.OnCurve; decide
private theorem validQ : C.Valid Q := by intro _; unfold Curve.OnCurve; decide

-- Genuine doubling and distinct addition witnesses use the complete constraint system.
example : E.CompleteCircuit P P Q := by
  apply (E.completeCircuit_iff hp hfit P P Q validP validP).mpr
  exact .double rfl rfl rfl 13 ⟨rfl, fun _ => by constructor <;> decide⟩
example : E.CompleteCircuit P Q ⟨⟨10,6⟩,false⟩ := by
  apply (E.completeCircuit_iff hp hfit _ _ _ validP validQ).mpr
  exact .distinct rfl rfl (by decide) 2 ⟨rfl, by constructor <;> decide⟩
example : E.CompleteCircuit P ⟨⟨5,16⟩,false⟩ ⟨⟨0,0⟩,true⟩ := by
  apply (E.completeCircuit_iff hp hfit _ _ _ validP (by intro _; unfold Curve.OnCurve; decide)).mpr
  exact .inverse rfl rfl rfl (by decide) rfl

-- Both infinity inputs may have different ignored coordinates: the left branch wins.
example : E.CompleteCircuit ⟨⟨5,1⟩,true⟩ ⟨⟨6,3⟩,true⟩ ⟨⟨6,3⟩,true⟩ := by
  apply (E.completeCircuit_iff hp hfit _ _ _ (by intro h; cases h) (by intro h; cases h)).mpr
  exact .left rfl rfl
example : E.CompleteCircuit ⟨⟨5,16⟩,true⟩ P P := by
  apply (E.completeCircuit_iff hp hfit _ _ _ (by intro h; cases h) validP).mpr
  exact .left rfl rfl
example : E.CompleteCircuit P ⟨⟨5,16⟩,true⟩ P := by
  apply (E.completeCircuit_iff hp hfit _ _ _ validP (by intro h; cases h)).mpr
  exact .right rfl rfl rfl

-- An off-curve output cannot pass any choice of raw selectors or quotient witnesses.
example : ¬ E.CompleteCircuit P Q ⟨⟨10,7⟩,false⟩ := by
  intro hc
  obtain ⟨hr, _⟩ := E.completeCircuit_sound hp hfit validP validQ hc
  exact (by unfold Curve.OnCurve; decide : ¬ C.OnCurve ⟨10,7⟩) (hr rfl)

-- The prover cannot turn all branches off, or claim equality of distinct coordinates.
example (bp bq zx zy : ℤ) (hl : bp = 0)
    (hr : selectRight bp bq = 0) (hi : selectInverse bp bq zx zy = 0)
    (hd : selectDouble bp bq zx zy = 0) (ha : selectAdd bp bq zx = 0) : False := by
  have h := selectors_partition bp bq zx zy
  omega
example (inv : Limbs 2) (hi : WellFormed E.params.B inv) :
    ¬ E.ZeroTest (E.canonicalLimbs 5) (E.canonicalLimbs 6) inv 1 := by
  intro hc
  have h := (E.zeroTest_selector hp (E.canonicalLimbs_bounded _) (E.canonicalLimbs_bounded _) hi hc).mp rfl
  simp only [E.limbValue_canonical] at h
  exact (by decide : (5 : ZMod 17) ≠ 6) h
example (inv : Limbs 2) (hi : WellFormed E.params.B inv) :
    ¬ E.ZeroTest (E.canonicalLimbs 5) (E.canonicalLimbs 5) inv 0 := by
  intro hc
  have h := (E.zeroTest_selector hp (E.canonicalLimbs_bounded _) (E.canonicalLimbs_bounded _) hi hc).mpr rfl
  omega

-- Equal residues need not share limb encodings: a native copy enforces actual wiring.
example : E.limbValue ![0,0] = E.limbValue ![2,3] := by decide
example : ¬ E.CopyLimbs 1 ![0,0] ![2,3] := by
  rw [E.copyLimbs_one_iff hfit (by unfold WellFormed; decide) (by unfold WellFormed; decide)]
  decide

end EfficientFFA.Tests.CompleteCircuit

#print axioms EfficientFFA.Native.ECEncoding.fixedGate_zero
#print axioms EfficientFFA.Native.ECEncoding.fixedGate_one_iff
#print axioms EfficientFFA.Native.ECEncoding.nativeBit_cases
#print axioms EfficientFFA.Native.ECEncoding.nativeBit_zero
#print axioms EfficientFFA.Native.ECEncoding.nativeBit_one
#print axioms EfficientFFA.Native.ECEncoding.copyLimbs_zero
#print axioms EfficientFFA.Native.ECEncoding.copyLimbs_one_iff
#print axioms EfficientFFA.Native.ECEncoding.exists_limbValue
#print axioms EfficientFFA.Native.ECEncoding.canonicalLimbs_bounded
#print axioms EfficientFFA.Native.ECEncoding.limbValue_canonical
#print axioms EfficientFFA.Native.ECEncoding.zero_limbs_bounded
#print axioms EfficientFFA.Native.ECEncoding.eqGate_zero
#print axioms EfficientFFA.Native.ECEncoding.negGate_zero
#print axioms EfficientFFA.Native.ECEncoding.invGate_zero
#print axioms EfficientFFA.Native.ECEncoding.eqGate_one_iff
#print axioms EfficientFFA.Native.ECEncoding.negGate_one_iff
#print axioms EfficientFFA.Native.ECEncoding.invGate_one_iff
#print axioms EfficientFFA.Native.ECEncoding.zeroTest_iff
#print axioms EfficientFFA.Native.ECEncoding.zeroTest_selector
#print axioms EfficientFFA.Native.ECEncoding.addGates_zero
#print axioms EfficientFFA.Native.ECEncoding.doubleGates_zero
#print axioms EfficientFFA.Native.ECEncoding.addGates_one_iff
#print axioms EfficientFFA.Native.ECEncoding.doubleGates_one_iff
#print axioms EfficientFFA.Native.ECEncoding.selectors_partition
#print axioms EfficientFFA.Native.ECEncoding.flagCopy_zero
#print axioms EfficientFFA.Native.ECEncoding.flagCopy_one_iff
#print axioms EfficientFFA.Native.ECEncoding.completeConstraints_sound
#print axioms EfficientFFA.Native.ECEncoding.copyLimbs_refl
#print axioms EfficientFFA.Native.ECEncoding.completeWires_bounded
#print axioms EfficientFFA.Native.ECEncoding.wireP_complete
#print axioms EfficientFFA.Native.ECEncoding.wireQ_complete
#print axioms EfficientFFA.Native.ECEncoding.wireR_complete
#print axioms EfficientFFA.Native.ECEncoding.decode_bitValue
#print axioms EfficientFFA.Native.ECEncoding.bitValue_nativeBit
#print axioms EfficientFFA.Native.ECEncoding.taggedP_complete
#print axioms EfficientFFA.Native.ECEncoding.taggedQ_complete
#print axioms EfficientFFA.Native.ECEncoding.taggedR_complete
#print axioms EfficientFFA.Native.ECEncoding.zeroTest_canonical
#print axioms EfficientFFA.Native.ECEncoding.completeCore_canonical
#print axioms EfficientFFA.Native.ECEncoding.addGates_complete_iff
#print axioms EfficientFFA.Native.ECEncoding.doubleGates_complete_iff
#print axioms EfficientFFA.Native.ECEncoding.completeConstraints_complete
#print axioms EfficientFFA.Native.ECEncoding.completeCircuit_iff
#print axioms EfficientFFA.Native.ECEncoding.completeCircuit_sound
#print axioms EfficientFFA.Native.ECEncoding.completeCircuit_complete
