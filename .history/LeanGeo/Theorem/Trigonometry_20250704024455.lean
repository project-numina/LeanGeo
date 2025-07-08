import Mathlib
import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Construction
import LeanGeo.Theorem.Area
namespace Trigonometrics
opaque
namespace LeanGeo
open LeanGeo

axiom rightAngle_eq_pi_div_two : ∟ = Real.pi / 2

axiom identity_sin : (a : ℝ) → sin a = Real.sin a
axiom identity_cos : (a : ℝ) → cos a = Real.cos a
axiom identity_tan : (a : ℝ) → tan a = Real.tan a

@[simp]
theorem sin_zero : sin 0 = 0 := by simp [identity_sin, Real.sin]

@[simp]
theorem sin_neg : ∀ (x : ℝ), sin (-x) = -sin x := by simp [identity_sin, Real.sin]

nonrec theorem sin_add : ∀ (x y : ℝ), sin (x + y) = sin x * cos y + cos x * sin y := by simp [identity_sin, identity_cos, Real.sin_add]

@[simp]
theorem cos_zero : cos 0 = 1 := by simp [identity_cos, Real.cos]

@[simp]
theorem cos_neg : ∀ (x : ℝ), cos (-x) = cos x := by simp [identity_cos, Real.cos]

nonrec theorem cos_add : ∀ (x y : ℝ), cos (x + y) = cos x * cos y - sin x * sin y := by simp [identity_sin, identity_cos, Real.cos_add]

theorem sin_sub : ∀ (x y: ℝ), sin (x - y) = sin x * cos y - cos x * sin y := by simp [identity_sin, identity_cos, Real.sin_sub]

theorem cos_sub : ∀ (x y: ℝ), cos (x - y) = cos x * cos y + sin x * sin y := by simp [identity_sin, identity_cos, Real.cos_sub]

nonrec theorem sin_sub_sin : ∀ (x y: ℝ), sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) := by simp [identity_sin, identity_cos, Real.sin_sub_sin]

nonrec theorem cos_sub_cos : ∀ (x y: ℝ), cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) := by simp [identity_sin, identity_cos, Real.cos_sub_cos]

nonrec theorem cos_add_cos : ∀ (x y: ℝ), cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := by simp [identity_cos, Real.cos_add_cos]

theorem two_mul_sin_mul_sin : ∀ (x y: ℝ), 2 * sin x * sin y = cos (x - y) - cos (x + y) := by
  intros
  simp only [cos_add, cos_sub]
  ring

theorem two_mul_cos_mul_cos : ∀ (x y: ℝ), 2 * cos x * cos y = cos (x - y) + cos (x + y) := by
  intros
  simp only [cos_add, cos_sub]
  ring

theorem two_mul_sin_mul_cos : ∀ (x y : ℝ), 2 * sin x * cos y = sin (x - y) + sin (x + y) := by
  intros
  simp only [sin_add, sin_sub]
  ring

nonrec theorem tan_eq_sin_div_cos : ∀ (x : ℝ), tan x = sin x / cos x := by simp [identity_sin, identity_cos, identity_tan, Real.tan_eq_sin_div_cos]

theorem tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel₀ _ hx]

@[simp]
theorem tan_zero : tan 0 = 0 := by simp [identity_tan, Real.tan]

@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [identity_tan, Real.tan]

@[simp]
nonrec theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 := by simp [identity_sin, identity_cos, Real.sin_sq_add_cos_sq]

@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by simp [identity_sin, identity_cos, Real.cos_sq_add_sin_sq]

theorem sin_sq_le_one : sin x ^ 2 ≤ 1 := by simp [identity_sin, Real.sin_sq_le_one, Real.abs_sin_le_one]

theorem cos_sq_le_one : cos x ^ 2 ≤ 1 := by simp [identity_cos, Real.cos_sq_le_one, Real.abs_cos_le_one]

theorem sin_le_one : sin x ≤ 1 := by simp [identity_sin, Real.sin_le_one]

theorem cos_le_one : cos x ≤ 1 := by simp [identity_cos, Real.cos_le_one]

theorem neg_one_le_sin : -1 ≤ sin x := by simp [identity_sin, Real.neg_one_le_sin]

theorem neg_one_le_cos : -1 ≤ cos x := by simp [identity_cos, Real.neg_one_le_cos]

nonrec theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 := by simp [identity_cos, Real.cos_two_mul]

nonrec theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by simp [identity_sin, identity_cos, Real.cos_two_mul']

nonrec theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x := by simp [identity_sin, identity_cos, Real.sin_two_mul]

nonrec theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 := by simp [identity_cos, Real.cos_sq]

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by simp [identity_sin, identity_cos, Real.cos_sq']

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 := by simp [identity_sin, identity_cos, Real.sin_sq]

lemma sin_sq_eq_half_sub : sin x ^ 2 = 1 / 2 - cos (2 * x) / 2 := by simp [identity_sin, identity_cos, Real.sin_sq_eq_half_sub]

theorem abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) : sin x = √(1 - cos x ^ 2) ∨ sin x = - √(1 - cos x ^ 2):= by
  euclid_intros
  sorry


theorem abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) : cos x = √(1 - sin x ^ 2) ∨ cos x = - √(1 - sin x ^ 2) := by
  euclid_intros
  euclid_finish
  /-rw [← cos_sq', sqrt_sq_eq_abs]-/

theorem inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 := by
  simp only [identity_cos] at hx
  simp only [identity_cos, identity_tan]
  apply Real.inv_one_add_tan_sq hx

theorem tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv]

theorem inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : (√(1 + tan x ^ 2))⁻¹ = cos x := by
  rw [← Real.sqrt_sq hx.le, ← Real.sqrt_inv, inv_one_add_tan_sq hx.ne']

theorem tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) :
    tan x / √(1 + tan x ^ 2) = sin x := by
  rw [← tan_mul_cos hx.ne', ← inv_sqrt_one_add_tan_sq hx, div_eq_mul_inv]

nonrec theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by sorry

nonrec theorem sin_three_mul : ∀ (x : ℝ), sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  euclid_intros
  have h1: x + 2*x = 3*x := by ring
  rw[← h1]
  euclid_apply sin_add x (2 * x)

  euclid_apply sin_two_mul
  euclid_finish



theorem sin_rightAngle : sin ∟ = 1 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.sin_pi_div_two]

theorem cos_rightAngle : cos ∟ = 0 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.cos_pi_div_two]

axiom rightTriangle_sin : ∀ (A B C : Point), rightTriangle A B C → sin (∠A:B:C) = |(A─C)| / |(B─C)|
axiom rightTriangle_cos : ∀ (A B C : Point), rightTriangle A B C → cos (∠B:C:A) = |(A─B)| / |(B─C)|

theorem traingle_area_sin : ∀ (A B C : Point), triangle A B C → (△A:B:C).area = |(A─B)| * |(A─C)| * sin (∠B:A:C) / 2 := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply exists_foot B AC as E
  euclid_apply triangle_area_foot B A C E AC
  by_cases (E ≠ A)
  · have h1: rightTriangle E A B := by
      sorry
    have h2: sin (∠B:A:C) = sin (∠E:A:B) := by
      sorry
    euclid_apply rightTriangle_sin E A B
    rw [h2, h_1]
    sorry
  · have h1: (∠B:A:C) = ∟ := by
      euclid_finish
    sorry

theorem law_of_sin : ∀ (A B C : Point), triangle A B C → |(B─C)| * sin (∠B:C:A)= |(A─B)| / sin (∠B:A:C)  := by
    sorry
    /-euclid_intros
    euclid_apply line_from_points B C as BC
    euclid_apply exists_foot A BC as H
    by_cases (H ≠ C) ∧ (H ≠ B)
    · euclid_apply rightTriangle_sin H C A
      euclid_apply rightTriangle_sin H B A-/

theorem law_of_cos : ∀ (A B C : Point), triangle A B C → |(A─B)| * |(A─B)| + |(A─C)| * |(A─C)| - |(B─C)| * |(B─C)| = 2 * cos (∠B:A:C) * |(A─B)| * |(A─C)| := by sorry

theorem thm1 : ∀ (A B C D : Point) (BC : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ D.onLine BC → |(D─C)| * |(A─B)| * sin (∠D:A:B) = |(D─B)| * |(A─C)| * sin (∠D:A:C) := by sorry

theorem cor1_1 : ∀ (A B C D : Point) (BC : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ D.onLine BC ∧ (∠D:A:B = ∠D:A:C) → |(D─C)| * |(A─B)| = |(D─B)| * |(A─C)| := by sorry

theorem cor1_2 : ∀ (A B C D : Point) (BC : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ D.onLine BC ∧ (|(D─B)| = |(D─C)|) → |(A─B)| * sin (∠D:A:B) = |(A─C)| * sin (∠D:A:C) := by sorry

theorem thm2 : ∀ (A B C D E F O: Point), (triangle A B C) ∧ coll A F B ∧ coll A E C ∧ coll B D C ∧ coll A O D ∧ coll C O F ∧ coll B O E → sin (∠D:A:B) * sin (∠E:B:C) * sin (∠F:C:A) = sin (∠D:A:C) * sin (∠E:B:A) * sin (∠F:C:B) := by sorry

theorem cor2_1 : ∀ (A B C D E F O: Point), (triangle A B C) ∧ coll A F B ∧ coll A E C ∧ coll B D C ∧ coll A O D ∧ coll C O F ∧ sin (∠D:A:B) * sin (∠E:B:C) * sin (∠F:C:A) = sin (∠D:A:C) * sin (∠E:B:A) * sin (∠F:C:B) → coll B O E:= by sorry

theorem thm3 : ∀ (A B C D E F O P: Point), (triangle A B C) ∧ coll A F B ∧ coll A E C ∧ coll B D C ∧ coll A O D ∧ coll C O F ∧ coll B O E ∧ ¬ P = D ∧ ¬ P = E ∧ ¬ P = F → sin (∠D:P:B) * sin (∠E:P:C) * sin (∠F:P:A) = sin (∠D:P:C) * sin (∠E:P:A) * sin (∠F:P:B) := by sorry

theorem cor3_1 : ∀ (A B C D E F O P: Point), (triangle A B C) ∧ coll A F B ∧ coll A E C ∧ coll B D C ∧ coll A O D ∧ coll C O F ∧ ¬ P = D ∧ ¬ P = E ∧ ¬ P = F ∧ sin (∠D:P:B) * sin (∠E:P:C) * sin (∠F:P:A) = sin (∠D:P:C) * sin (∠E:P:A) * sin (∠F:P:B) → coll B O E:= by sorry

theorem thm4 : ∀ (A B C L M N: Point) (AB BC CA l :Line), formTriangle A B C AB BC CA  ∧  L.onLine l ∧ L.onLine BC ∧ M.onLine l ∧ M.onLine CA ∧ N.onLine l ∧ N.onLine AB → sin (∠N:C:A) * sin (∠L:A:B) * sin (∠M:B:C) = sin (∠N:C:B) * sin (∠L:A:C) * sin (∠M:B:A) := by sorry

/-theorem cor4_1 :-/

theorem thm5 : ∀ (A B C L M N P: Point) (AB BC CA l :Line), formTriangle A B C AB BC CA  ∧  L.onLine l ∧ L.onLine BC ∧ M.onLine l ∧ M.onLine CA ∧ N.onLine l ∧ N.onLine AB ∧ ¬ P = L ∧ ¬ P = M ∧ ¬ P = N → sin (∠N:P:A) * sin (∠L:P:B) * sin (∠M:P:C) = sin (∠N:P:B) * sin (∠L:P:C) * sin (∠M:P:A) := by sorry

/-theorem cor5_1 :-/
