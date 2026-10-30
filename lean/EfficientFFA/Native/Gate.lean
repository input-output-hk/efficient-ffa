import EfficientFFA.Native.Polynomial

namespace EfficientFFA.Native
open Polynomial

structure Parameters (r : ℕ) where
  B : ℤ
  q : ℤ
  p : ℤ
  M : Fin r → ℤ
  t : ℕ
  tm : Fin r → ℕ

namespace Parameters
variable {r : ℕ} {α : Type*} (P : Parameters r)

def reduced (e : Polynomial α) := Polynomial.reduce P.q e
def residual (e : Polynomial α) (x : α → ℤ) := Polynomial.eval (P.reduced e) x
def A (e : Polynomial α) := -Polynomial.lower P.B (P.reduced e)
def C (e : Polynomial α) := Polynomial.upper P.B (P.reduced e)
def kmin (e : Polynomial α) := -(P.A e / P.q)
def kmax (e : Polynomial α) := P.C e / P.q
def Umax : ℤ := 2^P.t
def Vmax (a : Fin r) : ℤ := 2^(P.tm a)
def auxExpr (e : Polynomial α) (a : Fin r) := Polynomial.reduce (P.M a) (P.reduced e)
def Am (e : Polynomial α) (a : Fin r) :=
  -Polynomial.lower P.B (P.auxExpr e a) + P.Umax * (P.q % P.M a) + (P.kmin e * P.q) % P.M a
def Cm (e : Polynomial α) (a : Fin r) :=
  Polynomial.upper P.B (P.auxExpr e a) - (P.kmin e * P.q) % P.M a
def lmin (e : Polynomial α) (a : Fin r) := -(P.Am e a / P.M a)
def lmax (e : Polynomial α) (a : Fin r) := P.Cm e a / P.M a

def nativeResidual (e : Polynomial α) (x : α → ℤ) (u : ℤ) :=
  P.residual e x - (u+P.kmin e)*P.q
def auxCore (e : Polynomial α) (x : α → ℤ) (u : ℤ) (a : Fin r) :=
  Polynomial.eval (P.auxExpr e a) x - u*(P.q % P.M a) - (P.kmin e*P.q) % P.M a
def auxResidual (e : Polynomial α) (x : α → ℤ) (u v : ℤ) (a : Fin r) :=
  P.auxCore e x u a - (v+P.lmin e a)*P.M a

def L := moduliLCM (P.p :: List.ofFn P.M)
def auxLower (e : Polynomial α) (a : Fin r) := -P.Am e a - (P.Vmax a+P.lmin e a)*P.M a
def auxUpper (e : Polynomial α) (a : Fin r) := P.Cm e a - P.lmin e a*P.M a

structure Positive : Prop where
  radix : 0 < P.B
  foreign : 0 < P.q
  native : 0 < P.p
  auxiliary : ∀ a, 0 < P.M a
structure WidthBounds (e : Polynomial α) : Prop where
  native : P.kmax e-P.kmin e < P.Umax
  auxiliary : ∀ a, P.lmax e a-P.lmin e a < P.Vmax a
structure NoWrap (e : Polynomial α) : Prop where
  auxiliary_lower : ∀ a, -P.p < P.auxLower e a
  auxiliary_upper : ∀ a, P.auxUpper e a < P.p
  reconstruction_lower : P.A e+(P.Umax+P.kmin e)*P.q < P.L
  reconstruction_upper : P.C e-P.kmin e*P.q < P.L
structure Valid (e : Polynomial α) : Prop where
  positive : P.Positive
  widths : P.WidthBounds e
  nowrap : P.NoWrap e

/-- These are actual native-modulus polynomial equations and witness ranges. -/
structure Accepts (e : Polynomial α) (x : α → ℤ) (u : ℤ) (v : Fin r → ℤ) : Prop where
  u_range : 0 ≤ u ∧ u < P.Umax
  v_range : ∀ a, 0 ≤ v a ∧ v a < P.Vmax a
  native : P.nativeResidual e x u ≡ 0 [ZMOD P.p]
  auxiliary : ∀ a, P.auxResidual e x u (v a) a ≡ 0 [ZMOD P.p]

theorem residual_congr (e : Polynomial α) (x : α → ℤ) :
    P.residual e x ≡ Polynomial.eval e x [ZMOD P.q] := Polynomial.reduce_congr P.q e x

theorem residual_bounds (hP : P.Positive) (e : Polynomial α) {x : α → ℤ}
    (hx : Polynomial.Bounded P.B x) : -P.A e ≤ P.residual e x ∧ P.residual e x ≤ P.C e := by
  simpa only [A, C, residual, neg_neg] using Polynomial.eval_bounds P.B hP.radix (P.reduced e) hx

theorem auxCore_bounds (hP : P.Positive) (e : Polynomial α) {x : α → ℤ} {u : ℤ}
    (hx : Polynomial.Bounded P.B x) (hu : 0 ≤ u ∧ u < P.Umax) (a : Fin r) :
    -P.Am e a ≤ P.auxCore e x u a ∧ P.auxCore e x u a ≤ P.Cm e a := by
  have hb := Polynomial.eval_bounds P.B hP.radix (P.auxExpr e a) hx
  have hq : 0 ≤ P.q % P.M a := Int.emod_nonneg _ (ne_of_gt (hP.auxiliary a))
  have hu0 := mul_nonneg hu.1 hq
  have hu1 := mul_le_mul_of_nonneg_right (le_of_lt hu.2) hq
  dsimp [Am, Cm, auxCore]
  constructor <;> linarith

theorem auxCore_congr (e : Polynomial α) (x : α → ℤ) (u : ℤ) (a : Fin r) :
    P.auxCore e x u a ≡ P.nativeResidual e x u [ZMOD P.M a] := by
  have h := Polynomial.reduce_congr (P.M a) (P.reduced e) x
  have hq : P.q % P.M a ≡ P.q [ZMOD P.M a] := by simp [Int.ModEq]
  have hk : (P.kmin e*P.q) % P.M a ≡ P.kmin e*P.q [ZMOD P.M a] := by simp [Int.ModEq]
  have he := (h.sub ((Int.ModEq.refl u).mul hq)).sub hk
  simpa only [auxCore, auxExpr, nativeResidual, residual, add_mul, sub_add_eq_sub_sub] using he

/-- Native no-wrap and LCM reconstruction imply the foreign polynomial identity. -/
theorem sound {e : Polynomial α} (hP : P.Positive) (hnw : P.NoWrap e)
    {x : α → ℤ} {u : ℤ} {v : Fin r → ℤ}
    (hx : Polynomial.Bounded P.B x) (ha : P.Accepts e x u v) :
    Polynomial.eval e x ≡ 0 [ZMOD P.q] := by
  have haux : ∀ a, P.auxResidual e x u (v a) a = 0 := by
    intro a
    have hb := P.auxCore_bounds hP e hx ha.u_range a
    have hv := ha.v_range a
    have hm := hP.auxiliary a
    have hlo := hnw.auxiliary_lower a
    have hhi := hnw.auxiliary_upper a
    apply eq_zero_of_modEq_of_bounds (ha.auxiliary a)
    · dsimp [auxResidual, auxLower] at *; nlinarith
    · dsimp [auxResidual, auxUpper] at *; nlinarith
  have hm : ∀ a, P.nativeResidual e x u ≡ 0 [ZMOD P.M a] := by
    intro a
    have hd : P.M a ∣ P.auxCore e x u a := by
      refine ⟨v a+P.lmin e a, ?_⟩
      have he := haux a
      dsimp [auxResidual] at he
      nlinarith
    exact (P.auxCore_congr e x u a).symm.trans (Int.modEq_zero_iff_dvd.mpr hd)
  have hall : ∀ m ∈ P.p :: List.ofFn P.M, P.nativeResidual e x u ≡ 0 [ZMOD m] := by
    intro m hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ha.native
    · obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hmem
      exact hm a
  have hb := P.residual_bounds hP e hx
  have hu := ha.u_range
  have hq := hP.foreign
  have he : P.nativeResidual e x u = 0 := by
    apply eq_zero_of_congruences_of_bounds hall
    · have hlo := hnw.reconstruction_lower
      change -P.L < _
      dsimp [nativeResidual] at *
      nlinarith
    · have hhi := hnw.reconstruction_upper
      change _ < P.L
      dsimp [nativeResidual] at *
      nlinarith
  have hd : P.q ∣ P.residual e x := ⟨u+P.kmin e, by dsimp [nativeResidual] at he; nlinarith⟩
  exact (P.residual_congr e x).symm.trans (Int.modEq_zero_iff_dvd.mpr hd)

def witnessU (e : Polynomial α) (x : α → ℤ) := P.residual e x / P.q - P.kmin e
def witnessV (e : Polynomial α) (x : α → ℤ) (a : Fin r) :=
  P.auxCore e x (P.witnessU e x) a / P.M a - P.lmin e a

theorem witnesses_accept (hP : P.Positive) {e : Polynomial α} (hw : P.WidthBounds e)
    {x : α → ℤ} (hx : Polynomial.Bounded P.B x) (he : Polynomial.eval e x ≡ 0 [ZMOD P.q]) :
    P.Accepts e x (P.witnessU e x) (P.witnessV e x) := by
  have hd := Int.modEq_zero_iff_dvd.mp ((P.residual_congr e x).trans he)
  have hk := Int.ediv_mul_cancel hd
  have hb := P.residual_bounds hP e hx
  have hki := Multiplication.quotient_interval hP.foreign
    (show -P.A e ≤ (P.residual e x / P.q)*P.q by omega)
    (show (P.residual e x / P.q)*P.q ≤ P.C e by omega)
  have hu : 0 ≤ P.witnessU e x ∧ P.witnessU e x < P.Umax := by
    have := hw.native
    dsimp [witnessU, kmin, kmax] at *
    omega
  have hn : P.nativeResidual e x (P.witnessU e x) = 0 := by
    dsimp [nativeResidual, witnessU]
    rw [sub_add_cancel, hk, sub_self]
  have hav : ∀ a, (0 ≤ P.witnessV e x a ∧ P.witnessV e x a < P.Vmax a) ∧
      P.auxResidual e x (P.witnessU e x) (P.witnessV e x a) a = 0 := by
    intro a
    have hc : P.auxCore e x (P.witnessU e x) a ≡ 0 [ZMOD P.M a] := by
      simpa only [hn] using P.auxCore_congr e x (P.witnessU e x) a
    have hl := Int.ediv_mul_cancel (Int.modEq_zero_iff_dvd.mp hc)
    have hb := P.auxCore_bounds hP e hx hu a
    have hli := Multiplication.quotient_interval (hP.auxiliary a)
      (show -P.Am e a ≤ (P.auxCore e x (P.witnessU e x) a / P.M a)*P.M a by omega)
      (show (P.auxCore e x (P.witnessU e x) a / P.M a)*P.M a ≤ P.Cm e a by omega)
    constructor
    · have := hw.auxiliary a
      dsimp [witnessV, lmin, lmax] at *
      omega
    · dsimp [auxResidual, witnessV]
      rw [sub_add_cancel, hl, sub_self]
  exact ⟨hu, fun a => (hav a).1, by simp [hn], fun a => by simp [(hav a).2]⟩

theorem accepts_iff (e : Polynomial α) (hP : P.Valid e) {x : α → ℤ}
    (hx : Polynomial.Bounded P.B x) :
    (∃ u v, P.Accepts e x u v) ↔ Polynomial.eval e x ≡ 0 [ZMOD P.q] := by
  constructor
  · rintro ⟨u, v, ha⟩
    exact P.sound hP.positive hP.nowrap hx ha
  · intro he
    exact ⟨_, _, P.witnesses_accept hP.positive hP.widths hx he⟩

/-- Transport actual native polynomial checks to tracked bounded integer wires. -/
theorem accepts_of_rep {e : Polynomial α} {stored x : α → ℤ} {u : ℤ} {v : Fin r → ℤ}
    (hrep : ∀ a, stored a ≡ x a [ZMOD P.p]) (ha : P.Accepts e stored u v) : P.Accepts e x u v := by
  refine ⟨ha.u_range, ha.v_range, ?_, ?_⟩
  · exact ((Polynomial.eval_congr P.p (P.reduced e) hrep).sub (Int.ModEq.refl _)).symm.trans ha.native
  · intro a
    exact ((((Polynomial.eval_congr P.p (P.auxExpr e a) hrep).sub (Int.ModEq.refl _)).sub
      (Int.ModEq.refl _)).sub (Int.ModEq.refl _)).symm.trans (ha.auxiliary a)

end Parameters
end EfficientFFA.Native
