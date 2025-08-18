import Mathlib
import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Basic.Perpendicular
import LeanGeo.Theorem.Triangle.Basic

open Real
namespace LeanGeo

theorem sin_rightAngle : sin ∟ = 1 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.sin_pi_div_two]

theorem cos_rightAngle : cos ∟ = 0 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.cos_pi_div_two]

theorem straightAngle_eq_pi: ∟ + ∟ = Real.pi := by
  rw[rightAngle_eq_pi_div_two]
  linarith

theorem eq_sine_if_coll: ∀ (A B C D: Point), Coll A B C  ∧ (B ≠ C) ∧ (B ≠ A) ∧ (C ≠ A) ∧ ¬ (Coll A B D) →  sin (∠ D:B:C) = sin (∠ D:B:A) := by
  euclid_intros
  euclid_apply coll_eq_or_supp_angles A B C D
  by_cases ∠D:B:C = ∠D:B:A
  · euclid_finish
  · have h1: ∠ D:B:A = π/2 + π/2 - ∠ D:B:C := by
      rw[← rightAngle_eq_pi_div_two]
      euclid_finish
    have h2: ∠ D:B:A = π - ∠ D:B:C := by
      euclid_finish
    rw[h2,sin_pi_sub]

theorem triangleArea_sine : ∀ (A B C : Point), Triangle A B C → (△A:B:C).area = |(A─B)| * |(A─C)| * sin (∠B:A:C) / 2 := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply exists_foot B AC as E
  euclid_apply triangle_area_foot B A C E AC
  by_cases (E ≠ A)
  · have h1: RightTriangle E A B := by
      euclid_finish
    have h2: sin (∠B:A:C) = sin (∠E:A:B) := by
      euclid_apply eq_sine_if_coll
      euclid_finish
    have h3: sin (∠E:A:B) = |(E─B)| / |(A─B)| := by
      euclid_apply rightTriangle_sin E A B
      euclid_finish
    rw [h2, h3]
    euclid_finish
  · have h1: (∠B:A:C) = ∟ := by
      euclid_finish
    have h2: sin (∠B:A:C) = 1 := by
      euclid_apply rightAngle_eq_pi_div_two
      euclid_finish
    have h3: |(B─E)| * |(A─C)| / 2 = |(A─B)| * |(A─C)| / 2 := by
      euclid_finish
    euclid_finish

theorem LawOfSines : ∀ (A B C : Point), Triangle A B C → |(A─C)| * sin (∠B:C:A)= |(A─B)| * sin (∠A:B:C)  := by
    euclid_intros
    have h1 : |(B─C)| * |(A─C)| * sin (∠B:C:A)= |(B─C)| * |(A─B)| * sin (∠A:B:C) := by
      euclid_apply triangleArea_sine
      euclid_finish
    euclid_finish

theorem LawOfCosines : ∀ (A B C : Point), Triangle A B C → |(A─B)| * |(A─B)| + |(A─C)| * |(A─C)| - |(B─C)| * |(B─C)| = 2 * cos (∠B:A:C) * |(A─B)| * |(A─C)| := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply exists_foot B AC as H
  euclid_apply line_from_points B H as BH
  euclid_apply perpLine_imp_eq_sq_diff B H A C BH AC
  have h1: between A H C ∨ between H A C ∨ between A C H ∨ H = A ∨ H = C := by
    euclid_finish
  rcases h1 with h01|h02|h03|h04|h05
  · have h1: cos (∠B:A:C) = |(A─H)| / |(A─B)| := by
      have h2: ∠B:A:H = ∠B:A:C := by
        euclid_apply coll_angles_eq A H C B
        euclid_finish
      euclid_apply rightTriangle_cos H A B
      euclid_finish
    rw[h1]
    have h3: |(A─H)| + |(H─C)| = |(A─C)| := by
      euclid_finish
    euclid_finish
  · have h4: cos (∠B:A:C) = - (|(A─H)| / |(A─B)|):= by
      have h5: ∠B:A:C = ∟ + ∟ - ∠B:A:H:= by
        euclid_apply coll_angles_eq H A C B
        euclid_finish
      have h6: cos (∠B:A:H) = |(A─H)| / |(A─B)|:= by
        euclid_apply rightTriangle_cos H A B
        euclid_finish
      rw[h5, ←h6, straightAngle_eq_pi, Real.cos_pi_sub]
    rw[h4]
    have h7: |(A─H)| + |(A─C)| = |(H─C)| := by
      euclid_finish
    euclid_finish
  · have h1: cos (∠B:A:C) = |(A─H)| / |(A─B)| := by
      have h2: ∠B:A:H = ∠B:A:C := by
        euclid_apply coll_angles_eq A C H B
        euclid_finish
      euclid_apply rightTriangle_cos H A B
      euclid_finish
    rw[h1]
    have h3: |(A─C)| + |(H─C)| = |(A─H)| := by
      euclid_finish
    euclid_finish
  · have h1: ∠ B:A:C = ∟ := by
      euclid_finish
    rw[h1,cos_rightAngle]
    euclid_apply PythagoreanTheorem_point A B C
    euclid_finish
  · euclid_apply PythagoreanTheorem_point C B A
    euclid_apply rightTriangle_cos C A B
    euclid_finish

theorem GeneralizedAngleBisectorTheorem: ∀ (A B C D : Point), Triangle A B C ∧ Coll B C D → |(D─C)| * |(A─B)| * sin (∠D:A:B) = |(D─B)| * |(A─C)| * sin (∠D:A:C) := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points A C as AC
  by_cases D = B ∨ D = C
  · by_cases h2: D = B
    · have h1: ∠D:A:B = 0 := by
        euclid_finish
      euclid_apply Real.sin_zero
      euclid_finish
    · have h1: ∠D:A:C = 0 := by
        euclid_finish
      euclid_apply Real.sin_zero
      euclid_finish
  · have h1: |(A─B)| * sin (∠D:A:B) = |(B─D)| * sin (∠ A:D:B):= by
      euclid_apply LawOfSines B A D
      euclid_finish
    have h2: |(A─C)| * sin (∠D:A:C) = |(C─D)| * sin (∠ A:D:C):= by
      euclid_apply LawOfSines C A D
      euclid_finish
    have h3: sin (∠A:D:B) =  sin (∠A:D:C) := by
      euclid_apply eq_sine_if_coll B D C A
      euclid_finish
    euclid_finish

theorem GeneralizedAngleBisectorTheorem_to_midpoint : ∀ (A B C D : Point), Triangle A B C ∧ MidPoint B D C → |(A─B)| * sin (∠D:A:B) = |(A─C)| * sin (∠D:A:C) := by
  euclid_intros
  euclid_apply GeneralizedAngleBisectorTheorem A B C D
  euclid_finish

end LeanGeo
