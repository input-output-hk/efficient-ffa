import EfficientFFA.Multiplication
import EfficientFFA.Normalization
import EfficientFFA.Native

/-!
# Paper-facing mathematical contracts

Source: miguel-ambrona/ffa-paper at dddacd019ef180c1c6f1bfa06359bd59bf8c6733.
Names correspond to source labels, not unstable theorem or figure numbers.
These wrappers expose existing results. See PAPER_RESULTS_MAP.md for claim
IDs, parameter definitions and the correspondence boundary of each claim.

Multiplication uses floor/ceiling quotient rounding (M04). Complete addition
uses ordered branches (O04-O06), and MSM uses descending little-endian windows
(T08), as in the paper. Valid parameter bundles are mathematical hypotheses;
the paper's production choices are instantiated by the concrete certificates
in Instances/PaperParameters. Combined MSM contracts are in
Paper/MSMContract.lean.
-/

namespace EfficientFFA.Paper
open EllipticCurve Native MSM
open scoped ENNReal

section Arithmetic
variable {n r : ℕ}

/-- M12, thm:mul: equivalence on already supplied bounded limbs. -/
theorem multiplication_iff (P : Multiplication.Parameters n r) (hP : P.Valid)
    {x y z : Limbs n} (hx : WellFormed P.B x) (hy : WellFormed P.B y)
    (hz : WellFormed P.B z) :
    (∃ u v, P.Accepts x y z u v) ↔
      eval P.B x * eval P.B y ≡ eval P.B z [ZMOD P.q] :=
  P.accepts_iff_multiplication hP hx hy hz

/-- M10, thm:mul-soundness: no width-adequacy or capacity premise is needed. -/
theorem multiplication_sound (P : Multiplication.Parameters n r)
    (hP : P.Positive) (hnw : P.NoWrap) {x y z : Limbs n} {u : ℤ} {v : Fin r → ℤ}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (ha : P.Accepts x y z u v) :
    eval P.B x * eval P.B y ≡ eval P.B z [ZMOD P.q] :=
  P.multiplication_sound hP hnw hx hy hz ha

/-- M11, thm:mul-completeness: no no-wrap premise is needed in this direction. -/
theorem multiplication_complete (P : Multiplication.Parameters n r)
    (hP : P.Positive) (hw : P.WidthBounds) {x y z : Limbs n}
    (hx : WellFormed P.B x) (hy : WellFormed P.B y) (hz : WellFormed P.B z)
    (hmul : eval P.B x * eval P.B y ≡ eval P.B z [ZMOD P.q]) :
    ∃ u v, P.Accepts x y z u v :=
  P.multiplication_complete hP hw hx hy hz hmul

/-- L09, thm:normalization (first part): equality of foreign residues. -/
theorem normalization_iff (P : Normalization.Parameters n r) (hP : P.Valid)
    {x z : Limbs n} (hx : P.InputBounded x) (hz : WellFormed P.B z) :
    (∃ u v, P.Accepts x z u v) ↔ eval P.B x ≡ eval P.B z [ZMOD P.q] :=
  P.accepts_iff_normalization hP hx hz

/-- L10, thm:normalization (second part): capacity and adequate widths
construct a canonical output. -/
theorem normalization_exists (P : Normalization.Parameters n r)
    (hP : P.Positive) (hw : P.WidthBounds) (hcap : P.q ≤ P.B^n)
    {x : Limbs n} (hx : P.InputBounded x) :
    ∃ z u v, WellFormed P.B z ∧ P.Accepts x z u v ∧ eval P.B z = eval P.B x % P.q :=
  P.normalization_exists hP hw hcap hx

/-- L06: native residues retain the meaning of independently tracked signed limbs. -/
theorem stored_normalization_sound (P : Normalization.Parameters n r)
    (hP : P.Positive) (hnw : P.NoWrap) {stored x z : Limbs n}
    {u : ℤ} {v : Fin r → ℤ} (hs : LazyArithmetic.Represents P.p stored x)
    (hx : P.InputBounded x) (hz : WellFormed P.B z) (ha : P.Accepts stored z u v) :
    eval P.B x ≡ eval P.B z [ZMOD P.q] :=
  P.stored_normalization_sound hP hnw hs hx hz ha
end Arithmetic

section CompleteAddition
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

/-- O04: soundness of the ordered fig:complete-add contract. -/
theorem complete_add_sound {P Q R : Encoded K} (hP : C.Valid P) (hQ : C.Valid Q)
    (ha : C.CompleteAccepts P Q R) :
    ∃ hR : C.Valid R, C.decode R hR = C.decode P hP + C.decode Q hQ :=
  C.complete_sound hP hQ ha

/-- O04: every valid pair has an accepting output, including infinity and two-torsion. -/
theorem complete_add_complete {P Q : Encoded K} (hP : C.Valid P) (hQ : C.Valid Q) :
    ∃ R, C.CompleteAccepts P Q R ∧
      ∃ hR : C.Valid R, C.decode R hR = C.decode P hP + C.decode Q hQ :=
  C.complete_correct hP hQ
end CompleteAddition

section NativeEC
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

/-- E08/O04/O05: checked selectors and shared limbs implement the ordered relation.
Completeness is over decoded points, not arbitrary fixed public limb vectors. -/
theorem native_complete_add_iff {p : ℕ} [Fact p.Prime] (hp : E.params.p = p)
    (hfit : E.params.B ≤ E.params.p) (P Q R : Encoded (ZMod q))
    (hP : C.Valid P) (hQ : C.Valid Q) :
    E.CompleteCircuit P Q R ↔ C.CompleteAccepts P Q R :=
  E.completeCircuit_iff hp hfit P Q R hP hQ

/-- T17, soundness: arbitrary accepting linked traces compute the stated sum.
Windows are zero-indexed and processed in descending order. No prime group-order
or statistical size premise is needed for soundness. -/
theorem msm_sound {w l t : ℕ} {bases : ℕ → Coordinates (ZMod q)}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace (ZMod q)}
    (hbases : ∀ j, C.OnCurve (bases j))
    (ha : E.Trace w l t bases (descending windows t) tr) :
    ∃ hout : C.Valid tr.output, C.decode tr.output hout =
      ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
        C.point (bases j) (hbases j) :=
  E.trace_sound_littleEndian hbases ha

section WholeGroup
variable [Fintype C.Point] [DecidableEq C.Point]

/-- T17, statistical completeness: fixed inputs, uniform seed including zero.
The numerator includes setup failure as well as loop collisions. -/
theorem msm_failure_bound (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card C.Point : ℤ)) :
    (PMF.uniformOfFintype C.Point).toOuterMeasure
      {u | ¬ E.TraceWitnesses w l t bases (descending windows t) u} ≤
      ((1+l*(2^w+1)+2*t*l : ℕ) : ℝ≥0∞) / (Fintype.card C.Point : ℝ≥0∞) := by
  simpa only [failureBudget] using
    E.uniform_littleEndian_failure_bound w l t hw hl bases hbases windows hrange hprime hsize

/-- T17: the strictly smaller-than-cardinality budget yields a correct trace. -/
theorem msm_exists_correct (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card C.Point))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card C.Point : ℤ))
    (hbudget : 1+l*(2^w+1)+2*t*l < Fintype.card C.Point) :
    ∃ tr : CoordinateTrace (ZMod q), E.Trace w l t bases (descending windows t) tr ∧
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
          C.point (bases j) (hbases j) :=
  E.exists_correct_trace w l t hw hl bases hbases windows hrange hprime hsize hbudget
end WholeGroup

section Subgroup
variable (H : AddSubgroup C.Point) [Fintype H] [DecidableEq H]

/-- T14/T17: the same bound for uniform sampling within a prime-order subgroup.
The ambient curve may have a nontrivial cofactor. Input membership is explicit. -/
theorem msm_subgroup_failure_bound (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H) (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ)) :
    (PMF.uniformOfFintype H).toOuterMeasure
      {u | ¬ E.TraceWitnesses w l t bases (descending windows t) (u : C.Point)} ≤
      ((1+l*(2^w+1)+2*t*l : ℕ) : ℝ≥0∞) / (Fintype.card H : ℝ≥0∞) := by
  simpa only [failureBudget] using
    E.uniform_subgroup_failure_bound H w l t hw hl bases hbases hmem windows hrange hprime hsize

/-- T14/T17: witness existence also preserves subgroup membership of the output. -/
theorem msm_exists_correct_subgroup (w l t : ℕ) (hw : 0 < w) (hl : 0 < l)
    (bases : ℕ → Coordinates (ZMod q)) (hbases : ∀ j, C.OnCurve (bases j))
    (hmem : ∀ j, C.point (bases j) (hbases j) ∈ H) (windows : ℕ → ℕ → ℕ)
    (hrange : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w)
    (hprime : Nat.Prime (Nat.card H))
    (hsize : (2^w : ℕ)*(l : ℤ)+(2^w : ℕ)-1 < (Nat.card H : ℤ))
    (hbudget : 1+l*(2^w+1)+2*t*l < Fintype.card H) :
    ∃ u : H, ∃ tr : CoordinateTrace (ZMod q), E.Trace w l t bases (descending windows t) tr ∧
      (∃ hs : C.OnCurve tr.seed, C.point tr.seed hs = (u : C.Point)) ∧
      ∃ hout : C.Valid tr.output, C.decode tr.output hout =
        ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i*windows i j) •
          C.point (bases j) (hbases j) ∧ C.decode tr.output hout ∈ H :=
  E.exists_correct_subgroup_trace H w l t hw hl bases hbases hmem windows hrange hprime hsize hbudget
end Subgroup
end NativeEC
end EfficientFFA.Paper
