import EfficientFFA.Native.EllipticCurve
import EfficientFFA.MSM.TraceStatistics

namespace EfficientFFA.Native.ECEncoding
open EllipticCurve MSM
variable {q n r : ℕ} [Fact q.Prime] {C : Curve (ZMod q)} (E : ECEncoding C n r)

def bitValue (b : Bool) : ℤ := if b then 1 else 0

/-- The tag is represented by a native bit; equality to a branch tag is checked natively. -/
def Flag (b expected : Bool) : Prop :=
  bitValue b * (bitValue b-1) ≡ 0 [ZMOD E.params.p] ∧
  bitValue b ≡ bitValue expected [ZMOD E.params.p]

theorem flag_iff (b expected : Bool) : E.Flag b expected ↔ b = expected := by
  have hp := E.native_gt_one
  have h1 : (1 : ℤ) % E.params.p = 1 := Int.emod_eq_of_lt (by omega) hp
  cases b <;> cases expected <;> simp [Flag, bitValue, Int.ModEq, h1]

def EncodedCopy (P Q : Encoded (ZMod q)) := E.Copy P.coords Q.coords ∧ E.Flag P.infinity Q.infinity

theorem encodedCopy_iff (P Q : Encoded (ZMod q)) : E.EncodedCopy P Q ↔ P = Q := by
  rw [EncodedCopy, E.copy_iff, E.flag_iff]
  cases P; cases Q; simp

def Opposite (P Q : Coordinates (ZMod q)) := E.Equal P.x Q.x ∧ E.Negative P.y Q.y

theorem opposite_iff (P Q : Coordinates (ZMod q)) : E.Opposite P Q ↔ P = Curve.opposite Q := by
  rw [Opposite, E.equal_iff, E.negative_iff]
  cases P; cases Q; simp [Curve.opposite]

/-- The audited ordered Figure-3 refinement, with native arithmetic premises.
In particular no foreign-field AddChecks/DoubleChecks is an acceptance premise. -/
inductive Complete (P Q R : Encoded (ZMod q)) : Prop
  | left (hp : E.Flag P.infinity true) (hout : E.EncodedCopy R Q)
  | right (hp : E.Flag P.infinity false) (hq : E.Flag Q.infinity true) (hout : E.EncodedCopy R P)
  | inverse (hp : E.Flag P.infinity false) (hq : E.Flag Q.infinity false)
      (hx : E.Equal P.coords.x Q.coords.x) (hy : E.Negative P.coords.y Q.coords.y)
      (hr : E.Flag R.infinity true)
  | double (hp : E.Flag P.infinity false) (hq : E.Flag Q.infinity false)
      (he : E.Copy P.coords Q.coords) (hr : E.Flag R.infinity false)
      (s : ZMod q) (hc : E.Double P.coords R.coords s)
  | distinct (hp : E.Flag P.infinity false) (hq : E.Flag Q.infinity false)
      (hne : E.Distinct P.coords.x Q.coords.x) (hr : E.Flag R.infinity false)
      (s : ZMod q) (hc : E.Add P.coords Q.coords R.coords s)

theorem complete_iff (P Q R : Encoded (ZMod q)) : E.Complete P Q R ↔ C.CompleteAccepts P Q R := by
  constructor
  · intro h
    cases h with
    | left hp he =>
      exact .left ((E.flag_iff _ _).mp hp) ((E.encodedCopy_iff _ _).mp he)
    | right hp hq he =>
      exact .right ((E.flag_iff _ _).mp hp) ((E.flag_iff _ _).mp hq)
        ((E.encodedCopy_iff _ _).mp he)
    | inverse hp hq hx hy hr =>
      exact .inverse ((E.flag_iff _ _).mp hp) ((E.flag_iff _ _).mp hq)
        ((E.equal_iff _ _).mp hx) ((E.negative_iff _ _).mp hy) ((E.flag_iff _ _).mp hr)
    | double hp hq he hr s hc =>
      have hp' := (E.flag_iff _ _).mp hp
      exact .double hp' ((E.flag_iff _ _).mp hq) ((E.copy_iff _ _).mp he) s
        ⟨((E.flag_iff _ _).mp hr).trans hp'.symm, fun _ => (E.double_iff _ _ _).mp hc⟩
    | distinct hp hq hne hr s hc =>
      exact .distinct ((E.flag_iff _ _).mp hp) ((E.flag_iff _ _).mp hq)
        ((E.distinct_iff _ _).mp hne) s ⟨(E.flag_iff _ _).mp hr, (E.add_iff _ _ _ _).mp hc⟩
  · intro h
    cases h with
    | left hp he =>
      exact .left ((E.flag_iff _ _).mpr hp) ((E.encodedCopy_iff _ _).mpr he)
    | right hp hq he =>
      exact .right ((E.flag_iff _ _).mpr hp) ((E.flag_iff _ _).mpr hq)
        ((E.encodedCopy_iff _ _).mpr he)
    | inverse hp hq hx hy hr =>
      exact .inverse ((E.flag_iff _ _).mpr hp) ((E.flag_iff _ _).mpr hq)
        ((E.equal_iff _ _).mpr hx) ((E.negative_iff _ _).mpr hy) ((E.flag_iff _ _).mpr hr)
    | double hp hq he s hc =>
      exact .double ((E.flag_iff _ _).mpr hp) ((E.flag_iff _ _).mpr hq)
        ((E.copy_iff _ _).mpr he) ((E.flag_iff _ _).mpr (hc.1.trans hp)) s
        ((E.double_iff _ _ _).mpr (hc.2 hp))
    | distinct hp hq hne s hc =>
      exact .distinct ((E.flag_iff _ _).mpr hp) ((E.flag_iff _ _).mpr hq)
        ((E.distinct_iff _ _).mpr hne) ((E.flag_iff _ _).mpr hc.1) s ((E.add_iff _ _ _ _).mpr hc.2)

def Scale (seed : Coordinates (ZMod q)) (chain : ℕ → Encoded (ZMod q)) (steps : ℕ) :=
  E.Flag (chain 0).infinity true ∧
  ∀ k, k < steps → E.Complete (chain k) (finiteEncoding seed) (chain (k+1))

theorem scale_iff (seed : Coordinates (ZMod q)) (chain : ℕ → Encoded (ZMod q)) (steps : ℕ) :
    E.Scale seed chain steps ↔ C.ScaleChecks seed chain steps := by
  simp only [Scale, Curve.ScaleChecks, E.flag_iff, E.complete_iff]

/-- Native arithmetic trace. Range checks and semantic gate-port linkage are
explicit; PLONK permutation/lookup wiring is not modeled. -/
structure Trace (w l t : ℕ) (bases : ℕ → Coordinates (ZMod q))
    (windows : ℕ → ℕ → ℕ) (tr : CoordinateTrace (ZMod q)) : Prop where
  seed_on : E.OnCurve tr.seed
  offset_scale : E.Scale tr.seed tr.offsetChain (2^w-1)
  offset_end : E.EncodedCopy (tr.offsetChain (2^w-1)) (finiteEncoding tr.offset)
  initial_scale : E.Scale tr.seed tr.initialChain l
  initial_end : E.EncodedCopy (tr.initialChain l) (finiteEncoding (tr.boundary 0))
  table_zero : ∀ j, j < l → E.Opposite (tr.table j 0) tr.offset
  table_guard : ∀ j, j < l → E.Distinct (bases j).x tr.offset.x
  table_checks : ∀ j, j < l → ∀ k, k < 2^w-1 →
    ∃ s, E.Add (tr.table j k) (bases j) (tr.table j (k+1)) s
  window_range : ∀ i, i < t → ∀ j, j < l → windows i j < 2^w
  double_start : ∀ i, i < t → E.Copy (tr.doubles i 0) (tr.boundary i)
  double_checks : ∀ i, i < t → ∀ k, k < w → ∃ s, E.Double (tr.doubles i k) (tr.doubles i (k+1)) s
  row_start : ∀ i, i < t → E.Copy (tr.rows i 0) (tr.doubles i w)
  row_checks : ∀ i, i < t → ∀ j, j < l →
    E.Distinct (tr.rows i j).x (tr.table j (windows i j)).x ∧
    ∃ s, E.Add (tr.rows i j) (tr.table j (windows i j)) (tr.rows i (j+1)) s
  window_end : ∀ i, i < t → E.Copy (tr.boundary (i+1)) (tr.rows i l)
  final_check : ∃ neg, E.Opposite neg (tr.boundary 0) ∧
    E.Complete (finiteEncoding (tr.boundary t)) (finiteEncoding neg) tr.output

theorem trace_iff (w l t : ℕ) (bases : ℕ → Coordinates (ZMod q))
    (windows : ℕ → ℕ → ℕ) (tr : CoordinateTrace (ZMod q)) :
    E.Trace w l t bases windows tr ↔ C.TraceAccepts w l t bases windows tr := by
  constructor
  · intro h
    obtain ⟨neg, hn, hf⟩ := h.final_check
    have hn' := (E.opposite_iff _ _).mp hn
    refine ⟨(E.onCurve_iff _).mp h.seed_on, (E.scale_iff _ _ _).mp h.offset_scale,
      (E.encodedCopy_iff _ _).mp h.offset_end, (E.scale_iff _ _ _).mp h.initial_scale,
      (E.encodedCopy_iff _ _).mp h.initial_end,
      fun j hj => (E.opposite_iff _ _).mp (h.table_zero j hj),
      fun j hj => (E.distinct_iff _ _).mp (h.table_guard j hj), ?_, h.window_range,
      fun i hi => (E.copy_iff _ _).mp (h.double_start i hi), ?_,
      fun i hi => (E.copy_iff _ _).mp (h.row_start i hi), ?_,
      fun i hi => (E.copy_iff _ _).mp (h.window_end i hi), ?_⟩
    · intro j hj k hk
      simpa only [E.add_iff] using h.table_checks j hj k hk
    · intro i hi k hk
      simpa only [E.double_iff] using h.double_checks i hi k hk
    · intro i hi j hj
      simpa only [E.distinct_iff, E.add_iff] using h.row_checks i hi j hj
    · simpa only [hn'] using (E.complete_iff _ _ _).mp hf
  · intro h
    refine ⟨(E.onCurve_iff _).mpr h.seed_on, (E.scale_iff _ _ _).mpr h.offset_scale,
      (E.encodedCopy_iff _ _).mpr h.offset_end, (E.scale_iff _ _ _).mpr h.initial_scale,
      (E.encodedCopy_iff _ _).mpr h.initial_end,
      fun j hj => (E.opposite_iff _ _).mpr (h.table_zero j hj),
      fun j hj => (E.distinct_iff _ _).mpr (h.table_guard j hj), ?_, h.window_range,
      fun i hi => (E.copy_iff _ _).mpr (h.double_start i hi), ?_,
      fun i hi => (E.copy_iff _ _).mpr (h.row_start i hi), ?_,
      fun i hi => (E.copy_iff _ _).mpr (h.window_end i hi), ?_⟩
    · intro j hj k hk
      simpa only [E.add_iff] using h.table_checks j hj k hk
    · intro i hi k hk
      simpa only [E.double_iff] using h.double_checks i hi k hk
    · intro i hi j hj
      simpa only [E.distinct_iff, E.add_iff] using h.row_checks i hi j hj
    · exact ⟨_, (E.opposite_iff _ _).mpr rfl, (E.complete_iff _ _ _).mpr h.final_check⟩

/-- Native bounded-limb checks imply the MSM group result. The only foreign
curve-membership premise is for the public bases. -/
theorem trace_sound_littleEndian {w l t : ℕ} {bases : ℕ → Coordinates (ZMod q)}
    {windows : ℕ → ℕ → ℕ} {tr : CoordinateTrace (ZMod q)}
    (hbases : ∀ j, C.OnCurve (bases j))
    (ha : E.Trace w l t bases (descending windows t) tr) :
    ∃ hout : C.Valid tr.output, C.decode tr.output hout =
      ∑ j ∈ Finset.range l, (∑ i ∈ Finset.range t, (2^w)^i * windows i j) •
        C.point (bases j) (hbases j) :=
  C.trace_sound_littleEndian hbases ((E.trace_iff _ _ _ _ _ _).mp ha)

end EfficientFFA.Native.ECEncoding
