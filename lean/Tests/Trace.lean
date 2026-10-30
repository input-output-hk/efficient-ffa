import EfficientFFA
import Tests.Tables

namespace EfficientFFA.Tests.Trace
open EllipticCurve MSM
private abbrev C := Tables.C17
private abbrev P := Tables.base17
private abbrev P2 := Tables.twice17
private abbrev U := Tables.three17
private def P4 : Coordinates (ZMod 17) := ⟨3, 1⟩
private def P5 : Coordinates (ZMod 17) := ⟨9, 16⟩
private def P6 : Coordinates (ZMod 17) := ⟨16, 13⟩
private def P8 : Coordinates (ZMod 17) := ⟨13, 7⟩
private def negU : Coordinates (ZMod 17) := ⟨10, 11⟩
private def negP2 : Coordinates (ZMod 17) := ⟨6, 14⟩
private def bases : ℕ → Coordinates (ZMod 17) := fun _ => P
private def digits : ℕ → ℕ → ℕ := fun i _ => if i = 0 then 0 else 1
private def chain : ℕ → Encoded (ZMod 17) :=
  fun k => if k = 0 then ⟨U, true⟩ else finiteEncoding U
private def boundary : ℕ → Coordinates (ZMod 17)
  | 0 => U
  | 1 => P4
  | _ => P5
private def doubles : ℕ → ℕ → Coordinates (ZMod 17) :=
  fun i k => if k = 0 then boundary i else if i = 0 then P6 else P8
private def rows : ℕ → ℕ → Coordinates (ZMod 17) :=
  fun i j => if j = 0 then doubles i 1 else boundary (i+1)
private def tr : CoordinateTrace (ZMod 17) where
  seed := U
  offset := U
  offsetChain := chain
  initialChain := chain
  table := fun _ k => if k = 0 then negU else negP2
  boundary := boundary
  doubles := doubles
  rows := rows
  output := finiteEncoding P2

private theorem scale_ok : C.ScaleChecks U chain 1 := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have he : k = 0 := by omega
  subst k
  exact .left rfl rfl

-- A complete accepted two-window trace, including constant chains, table and final output.
theorem accepted : C.TraceAccepts 1 1 2 bases (descending digits 2) tr := by
  constructor
  · unfold Curve.OnCurve
    decide
  · exact scale_ok
  · rfl
  · exact scale_ok
  · rfl
  · intro j _
    rfl
  · intro j hj
    have he : j = 0 := by omega
    subst j
    decide
  · intro j hj k hk
    have hj0 : j = 0 := by omega
    subst j
    have he : k = 0 := by omega
    subst k
    exact ⟨2, by constructor <;> decide⟩
  · intro i hi j hj
    have hj0 : j = 0 := by omega
    subst j
    interval_cases i <;> decide
  · intro i _
    rfl
  · intro i hi k hk
    have he : k = 0 := by omega
    subst k
    interval_cases i
    · exact ⟨11, by constructor <;> decide⟩
    · exact ⟨6, by constructor <;> decide⟩
  · intro i _
    rfl
  · intro i hi j hj
    have he : j = 0 := by omega
    subst j
    interval_cases i
    · exact ⟨by decide, 5, by constructor <;> decide⟩
    · exact ⟨by decide, 10, by constructor <;> decide⟩
  · intro i hi
    interval_cases i <;> rfl
  · exact .distinct rfl rfl (by decide) 12 ⟨rfl, by constructor <;> decide⟩

-- The composed soundness theorem certifies the result for the supplied trace.
example : ∃ hout : C.Valid tr.output, C.decode tr.output hout =
    ∑ j ∈ Finset.range 1, (∑ i ∈ Finset.range 2, (2^1)^i * digits i j) •
      C.point (bases j) Tables.base17_on :=
  C.trace_sound_littleEndian (fun _ => Tables.base17_on) accepted

-- Substituting a wrong output cannot satisfy the trace contract.
example : ¬ C.TraceAccepts 1 1 2 bases (descending digits 2)
    {tr with output := finiteEncoding P} := by
  intro hbad
  obtain ⟨hv, he⟩ := C.trace_sound_littleEndian (fun _ => Tables.base17_on) hbad
  obtain ⟨hv', he'⟩ := C.trace_sound_littleEndian (fun _ => Tables.base17_on) accepted
  have hg := he.trans he'.symm
  have hp : C.point P Tables.base17_on = C.point P2 Tables.twice17_on := by
    simpa [tr, Curve.decode, finiteEncoding] using hg
  exact (by decide : P ≠ P2) (C.point_injective hp)

-- The initial-accumulator link is enforced even when the substitute is on the curve.
example : ¬ C.TraceAccepts 1 1 2 bases (descending digits 2)
    {tr with boundary := fun _ => P} := by
  intro hbad
  have he := hbad.initial_end
  exact (by decide : chain 1 ≠ finiteEncoding P) he

-- A nonempty execution with a zero scalar needs a genuine infinity output.
private def zeroTrace : CoordinateTrace (ZMod 17) := {
  tr with boundary := fun _ => U,
          rows := fun _ j => if j = 0 then P6 else U,
          output := ⟨⟨0, 0⟩, true⟩ }

theorem accepted_zero : C.TraceAccepts 1 1 1 bases (fun _ _ => 0) zeroTrace := by
  constructor
  · exact accepted.seed_on
  · exact scale_ok
  · rfl
  · exact scale_ok
  · rfl
  · intro j _
    rfl
  · intro j hj
    have he : j = 0 := by omega
    subst j
    decide
  · exact accepted.table_checks
  · intro i _ j _
    decide
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rfl
  · intro i hi k hk
    have hi0 : i = 0 := by omega
    have hk0 : k = 0 := by omega
    subst i; subst k
    exact ⟨11, by constructor <;> decide⟩
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rfl
  · intro i hi j hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst i; subst j
    exact ⟨by decide, 6, by constructor <;> decide⟩
  · intro i _
    rfl
  · exact .inverse rfl rfl (by decide) (by decide) rfl

example : ∃ hv : C.Valid zeroTrace.output, C.decode zeroTrace.output hv = 0 := by
  have h := C.trace_sound_littleEndian (fun _ => Tables.base17_on)
    (windows := fun _ _ => 0) accepted_zero
  simpa using h

-- The same complete supplied traces also admit all native limb/quotient witnesses.
example : Instances.Curve17.encoding.Trace 1 1 2 bases (descending digits 2) tr :=
  (Instances.Curve17.encoding.trace_iff _ _ _ _ _ _).mpr accepted
example : Instances.Curve17.encoding.Trace 1 1 1 bases (fun _ _ => 0) zeroTrace :=
  (Instances.Curve17.encoding.trace_iff _ _ _ _ _ _).mpr accepted_zero
example : ¬ Instances.Curve17.encoding.Trace 1 1 2 bases (descending digits 2)
    {tr with boundary := fun _ => P} := by
  intro hbad
  have he := ((Instances.Curve17.encoding.trace_iff _ _ _ _ _ _).mp hbad).initial_end
  exact (by decide : chain 1 ≠ finiteEncoding P) he

end EfficientFFA.Tests.Trace

#print axioms EfficientFFA.EllipticCurve.Curve.scale_sound
#print axioms EfficientFFA.EllipticCurve.Curve.encoded_eq_finite
#print axioms EfficientFFA.EllipticCurve.Curve.scale_exists
#print axioms EfficientFFA.EllipticCurve.Curve.scale_exists_to
#print axioms EfficientFFA.EllipticCurve.Curve.scale_finite_sound
#print axioms EfficientFFA.EllipticCurve.Curve.trace_setup
#print axioms EfficientFFA.EllipticCurve.Curve.trace_lookup
#print axioms EfficientFFA.EllipticCurve.Curve.trace_doubles
#print axioms EfficientFFA.EllipticCurve.Curve.trace_rows
#print axioms EfficientFFA.EllipticCurve.Curve.trace_boundaries
#print axioms EfficientFFA.EllipticCurve.Curve.trace_sound
#print axioms EfficientFFA.EllipticCurve.Curve.trace_sound_littleEndian
#print axioms EfficientFFA.EllipticCurve.Curve.coordinates_add_witnesses
#print axioms EfficientFFA.EllipticCurve.Curve.coordinates_point
#print axioms EfficientFFA.EllipticCurve.Curve.coordinates_neg
#print axioms EfficientFFA.EllipticCurve.Curve.canonical_table_checks
#print axioms EfficientFFA.EllipticCurve.Curve.canonical_table_guard
#print axioms EfficientFFA.EllipticCurve.Curve.trace_complete
#print axioms EfficientFFA.MSM.descending_range
#print axioms EfficientFFA.EllipticCurve.Curve.uniform_trace_failure_bound_prime
#print axioms EfficientFFA.EllipticCurve.Curve.uniform_littleEndian_trace_failure_bound_prime
#print axioms EfficientFFA.EllipticCurve.Curve.exists_trace_prime
#print axioms EfficientFFA.EllipticCurve.Curve.exists_correct_trace_prime
