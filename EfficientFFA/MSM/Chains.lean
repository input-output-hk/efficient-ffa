import EfficientFFA.MSM.Safety

namespace EfficientFFA.EllipticCurve
/-- A finite affine point with its explicit Boolean tag. -/
def finiteEncoding {K : Type*} (P : Coordinates K) : Encoded K := ⟨P, false⟩

namespace Curve
variable {K : Type*} [Field K] [DecidableEq K] (C : Curve K)

/-- Complete-add chain enforcing multiplication by a fixed natural scalar.
The starting point is infinity; each link adds the same finite seed. -/
def ScaleChecks (seed : Coordinates K) (chain : ℕ → Encoded K) (n : ℕ) : Prop :=
  (chain 0).infinity = true ∧
  ∀ k, k < n → C.CompleteAccepts (chain k) (finiteEncoding seed) (chain (k+1))

theorem scale_sound {seed : Coordinates K} {chain : ℕ → Encoded K} {n : ℕ}
    (hseed : C.OnCurve seed) (hc : C.ScaleChecks seed chain n) :
    ∀ k, k ≤ n → ∃ hk : C.Valid (chain k),
      C.decode (chain k) hk = k • C.point seed hseed := by
  intro k
  induction k with
  | zero =>
    intro _
    have hv : C.Valid (chain 0) := by intro h; simp_all [hc.1]
    exact ⟨hv, by rw [C.decode_infinity hv hc.1, zero_nsmul]⟩
  | succ k ih =>
    intro hk
    obtain ⟨hv, he⟩ := ih (by omega)
    obtain ⟨hv', he'⟩ := C.complete_sound hv (show C.Valid (finiteEncoding seed) from fun _ => hseed)
      (hc.2 k (by omega))
    rw [he, C.decode_finite (P := finiteEncoding seed) _ rfl] at he'
    exact ⟨hv', by simpa only [finiteEncoding, succ_nsmul] using he'⟩

omit [DecidableEq K] in
/-- Any valid representation of a nonidentity point has the unique finite coordinates. -/
theorem encoded_eq_finite {R : Encoded K} (hR : C.Valid R) {P : Coordinates K}
    (hP : C.OnCurve P) (he : C.decode R hR = C.point P hP) : R = finiteEncoding P := by
  have hr : R.infinity = false := by
    cases hh : R.infinity
    · rfl
    · exact False.elim (C.point_ne_zero hP (he.symm.trans (C.decode_infinity hR hh)))
  have hc : R.coords = P := C.point_injective ((C.decode_finite hR hr).symm.trans he)
  cases R
  simp_all [finiteEncoding]

/-- Constant multiplication always has a complete-add chain. -/
theorem scale_exists (seed : Coordinates K) (hseed : C.OnCurve seed) (n : ℕ) :
    ∃ chain, C.ScaleChecks seed chain n := by
  induction n with
  | zero => exact ⟨fun _ => ⟨seed, true⟩, rfl, by intro k hk; omega⟩
  | succ n ih =>
    obtain ⟨chain, hc⟩ := ih
    obtain ⟨hv, _⟩ := C.scale_sound hseed hc n (by omega)
    obtain ⟨R, hR⟩ := C.complete_exists hv (show C.Valid (finiteEncoding seed) from fun _ => hseed)
    refine ⟨fun k => if k = n+1 then R else chain k, ?_, ?_⟩
    · simpa using hc.1
    · intro k hk
      by_cases hn : k < n
      · have hkn : k ≠ n+1 := by omega
        have hks : k+1 ≠ n+1 := by omega
        simpa only [if_neg hkn, if_neg hks] using hc.2 k hn
      · have he : k = n := by omega
        subst k
        simpa using hR

/-- Endpoint linkage is enforced by coordinate equality, not a presumed group product. -/
theorem scale_exists_to {seed target : Coordinates K}
    (hseed : C.OnCurve seed) (htarget : C.OnCurve target) (n : ℕ)
    (he : C.point target htarget = n • C.point seed hseed) :
    ∃ chain, C.ScaleChecks seed chain n ∧ chain n = finiteEncoding target := by
  obtain ⟨chain, hc⟩ := C.scale_exists seed hseed n
  obtain ⟨hv, hg⟩ := C.scale_sound hseed hc n (by omega)
  exact ⟨chain, hc, C.encoded_eq_finite hv htarget (hg.trans he.symm)⟩

/-- A finite endpoint of an accepted chain has the derived scalar meaning. -/
theorem scale_finite_sound {seed target : Coordinates K} {chain : ℕ → Encoded K} {n : ℕ}
    (hseed : C.OnCurve seed) (hc : C.ScaleChecks seed chain n)
    (hend : chain n = finiteEncoding target) :
    ∃ ht : C.OnCurve target, C.point target ht = n • C.point seed hseed := by
  obtain ⟨hv, he⟩ := C.scale_sound hseed hc n (by omega)
  have hv' : C.Valid (finiteEncoding target) := by simpa only [hend] using hv
  have he' : C.decode (finiteEncoding target) hv' = n • C.point seed hseed := by
    simpa only [hend] using he
  exact ⟨hv' rfl, by simpa [decode, finiteEncoding] using he'⟩

end Curve
end EfficientFFA.EllipticCurve
