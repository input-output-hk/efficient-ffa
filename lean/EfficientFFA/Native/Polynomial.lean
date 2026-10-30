import EfficientFFA.Multiplication.Bounds

namespace EfficientFFA.Native

/-- A sparse integer polynomial. A monomial is a list of input-wire indices.
Repeated indices represent powers; the empty monomial is the constant one. -/
abbrev Polynomial (α : Type*) := List (ℤ × List α)

namespace Polynomial
variable {α : Type*}

def monomial (vars : List α) (x : α → ℤ) : ℤ := (vars.map x).prod
def eval (e : Polynomial α) (x : α → ℤ) : ℤ :=
  (e.map (fun t => t.1 * monomial t.2 x)).sum

def constant (c : ℤ) : Polynomial α := [(c, [])]
def wire (a : α) : Polynomial α := [(1, [a])]
def add (e f : Polynomial α) : Polynomial α := e ++ f
def scale (c : ℤ) (e : Polynomial α) : Polynomial α := e.map (fun t => (c*t.1, t.2))
def mul (e f : Polynomial α) : Polynomial α :=
  e.flatMap (fun t => f.map (fun s => (t.1*s.1, t.2++s.2)))
def sub (e f : Polynomial α) : Polynomial α := add e (scale (-1) f)

theorem eval_constant (c : ℤ) (x : α → ℤ) : eval (constant c) x = c := by
  simp [eval, constant, monomial]
theorem eval_wire (a : α) (x : α → ℤ) : eval (wire a) x = x a := by
  simp [eval, wire, monomial]
theorem eval_add (e f : Polynomial α) (x : α → ℤ) :
    eval (add e f) x = eval e x + eval f x := by simp [eval, add]
theorem eval_scale (c : ℤ) (e : Polynomial α) (x : α → ℤ) :
    eval (scale c e) x = c * eval e x := by
  induction e with
  | nil => simp [eval, scale]
  | cons t e ih => simp only [scale, List.map_cons, eval, List.sum_cons] at ih ⊢; rw [ih]; ring

theorem eval_mul (e f : Polynomial α) (x : α → ℤ) :
    eval (mul e f) x = eval e x * eval f x := by
  induction e with
  | nil => simp [eval, mul]
  | cons t e ih =>
    simp only [mul, List.flatMap_cons, eval, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have ht : ((f.map fun s => (t.1*s.1, t.2++s.2)).map
        (fun s => s.1 * monomial s.2 x)).sum = t.1 * monomial t.2 x * eval f x := by
      clear ih
      induction f with
      | nil => simp [eval]
      | cons s f ihf =>
        simp only [List.map_cons, List.sum_cons, eval] at ihf ⊢
        simp only [monomial, List.map_append, List.prod_append] at ihf ⊢
        rw [ihf]
        ring
    rw [ht]
    simp only [eval]
    ring

theorem eval_sub (e f : Polynomial α) (x : α → ℤ) :
    eval (sub e f) x = eval e x - eval f x := by
  rw [sub, eval_add, eval_scale]
  ring

/-- Coefficient reduction preserves the sign convention of the paper's identities. -/
def signedMod (m c : ℤ) : ℤ := if c < 0 then -((-c) % m) else c % m

theorem signedMod_congr (m c : ℤ) : signedMod m c ≡ c [ZMOD m] := by
  unfold signedMod
  split_ifs
  · have h : (-c) % m ≡ -c [ZMOD m] := by simp [Int.ModEq]
    simpa using h.neg
  · simp [Int.ModEq]

def reduce (m : ℤ) (e : Polynomial α) : Polynomial α :=
  e.map (fun t => (signedMod m t.1, t.2))

theorem reduce_congr (m : ℤ) (e : Polynomial α) (x : α → ℤ) :
    eval (reduce m e) x ≡ eval e x [ZMOD m] := by
  induction e with
  | nil => exact Int.ModEq.refl _
  | cons t e ih =>
    exact ((signedMod_congr m t.1).mul (Int.ModEq.refl _)).add ih

/-- Worst-case bounds computed from the coefficients and monomial degrees. -/
def lower (B : ℤ) (e : Polynomial α) : ℤ :=
  (e.map (fun t => min t.1 0 * (B-1)^t.2.length)).sum
def upper (B : ℤ) (e : Polynomial α) : ℤ :=
  (e.map (fun t => max t.1 0 * (B-1)^t.2.length)).sum

def Bounded (B : ℤ) (x : α → ℤ) : Prop := ∀ a, 0 ≤ x a ∧ x a < B

theorem monomial_bounds (B : ℤ) (hB : 0 < B) (vars : List α) {x : α → ℤ}
    (hx : Bounded B x) : 0 ≤ monomial vars x ∧ monomial vars x ≤ (B-1)^vars.length := by
  induction vars with
  | nil => simp [monomial]
  | cons a vars ih =>
    have ha := hx a
    have hpow : 0 ≤ (B-1)^vars.length := pow_nonneg (by omega) _
    simp only [monomial, List.map_cons, List.prod_cons, List.length_cons, pow_succ] at ih ⊢
    constructor
    · exact mul_nonneg ha.1 ih.1
    · nlinarith [mul_le_mul (show x a ≤ B-1 by omega) ih.2 ih.1 (show 0 ≤ B-1 by omega)]

theorem eval_bounds (B : ℤ) (hB : 0 < B) (e : Polynomial α) {x : α → ℤ}
    (hx : Bounded B x) : lower B e ≤ eval e x ∧ eval e x ≤ upper B e := by
  induction e with
  | nil => simp [lower, upper, eval]
  | cons t e ih =>
    have hm := monomial_bounds B hB t.2 hx
    have hlo : min t.1 0 * (B-1)^t.2.length ≤ t.1 * monomial t.2 x := by
      by_cases hc : 0 ≤ t.1
      · rw [min_eq_right hc]
        exact (zero_mul _).trans_le (mul_nonneg hc hm.1)
      · rw [min_eq_left (by omega)]
        exact mul_le_mul_of_nonpos_left hm.2 (by omega)
    have hhi : t.1 * monomial t.2 x ≤ max t.1 0 * (B-1)^t.2.length := by
      by_cases hc : 0 ≤ t.1
      · rw [max_eq_left hc]
        exact mul_le_mul_of_nonneg_left hm.2 hc
      · rw [max_eq_right (by omega)]
        simpa using mul_nonpos_of_nonpos_of_nonneg (show t.1 ≤ 0 by omega) hm.1
    simp only [lower, upper, eval, List.map_cons, List.sum_cons] at ih ⊢
    constructor <;> linarith

/-- Native residues can be substituted without changing a polynomial check modulo p. -/
theorem eval_congr (p : ℤ) (e : Polynomial α) {x y : α → ℤ}
    (hxy : ∀ a, x a ≡ y a [ZMOD p]) : eval e x ≡ eval e y [ZMOD p] := by
  have hm : ∀ vars : List α, monomial vars x ≡ monomial vars y [ZMOD p] := by
    intro vars
    induction vars with
    | nil => exact Int.ModEq.refl _
    | cons a vars ih => exact (hxy a).mul ih
  induction e with
  | nil => exact Int.ModEq.refl _
  | cons t e ih => exact ((Int.ModEq.refl t.1).mul (hm t.2)).add ih

end Polynomial
end EfficientFFA.Native
