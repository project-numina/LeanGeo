import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Perpendicular
import LeanGeo.Theorem.Basic.PerpBisector
import LeanGeo.Theorem.Triangle.Basic
import LeanGeo.Theorem.Circle.Basic

open Real
namespace LeanGeo

theorem exists_circumcentre: ∀(A B C : Point), Triangle A B C → ∃(O : Point), Circumcentre O A B C := by
  euclid_intros
  euclid_apply threePoints_existCircle A B C as Ω
  euclid_apply exists_centre Ω as O
  use O
  euclid_finish

theorem triangle_perpBisectors_concurrent: ∀(A B C: Point) (l1 l2 l3: Line), Triangle A B C ∧ PerpBisector A B l1 ∧ PerpBisector B C l2 ∧ PerpBisector A C l3 → Concurrent l1 l2 l3 := by
  euclid_intros
  euclid_apply exists_circumcentre A B C as O
  use O
  euclid_apply perpBisector_imp_eq_dist
  euclid_finish

theorem acuteTriangle_circumcentre_insideTriangle: ∀(A B C O: Point) (AB BC CA : Line),formTriangle A B C AB BC CA ∧ AcuteTriangle A B C ∧ Circumcentre O A B C → InsideTriangle O A B C AB BC CA := by
  euclid_intros
  euclid_apply circle_from_points O A as Ω
  have h1: O.sameSide A BC := by
    by_contra
    by_cases O.opposingSides A BC
    · euclid_apply InscribedAngleTheorem_opposingSides C B A O BC Ω
      euclid_finish
    · euclid_apply ThalesTheorem B C A O Ω
      euclid_finish
  have h1: O.sameSide B CA := by
    by_contra
    by_cases O.opposingSides B CA
    · euclid_apply InscribedAngleTheorem_opposingSides A C B O CA Ω
      euclid_finish
    · euclid_apply ThalesTheorem C A B O Ω
      euclid_finish
  have h1: O.sameSide C AB := by
    by_contra
    by_cases O.opposingSides C AB
    · euclid_apply InscribedAngleTheorem_opposingSides B A C O AB Ω
      euclid_finish
    · euclid_apply ThalesTheorem A B C O Ω
      euclid_finish
  euclid_finish

theorem isoTriangle_base_side_cos : ∀(A B C : Point), |(A─B)| = |(A─C)| ∧ B ≠ C → 2 * |(A─B)| * cos (∠A:B:C) = |(B─C)| := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  by_cases Coll A B C
  · euclid_assert MidPoint B A C
    have  h1: 2 * |(A─B)| = |(B─C)| := by
      euclid_finish
    have h2: ∠ A:B:C = 0 := by
      euclid_finish
    euclid_apply Real.cos_zero
    euclid_finish
  · euclid_apply exists_midpoint B C as D
    have h1: ∠B:D:A = ∟ := by
      euclid_apply isoTriangle_three_lines_concidence_midpoint A B C D
      euclid_finish
    euclid_apply rightTriangle_cos D B A
    have h3 : ∠D:B:A = ∠A:B:C :=by
      euclid_apply coll_angles_eq
      euclid_finish
    euclid_finish

theorem circumcentre_inscribedAngle_comp : ∀ (A B C O : Point) (AB: Line) (Ω : Circle), (distinctPointsOnLine A B AB) ∧ (O.sameSide C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
  → ∠ O:B:A +  ∠ A:C:B= ∟ := by
  euclid_intros
  euclid_apply InscribedAngleTheorem_sameSide A B C O AB Ω
  euclid_apply isoTriangle_imp_eq_angles O A B
  euclid_apply triangle_angles_sum O A B
  euclid_finish

theorem circumcentre_inscribedAngle_diff_rightAngle : ∀ (A B C O : Point) (AB: Line) (Ω : Circle), (distinctPointsOnLine A B AB) ∧ (O.opposingSides C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
  → ∠ A:C:B - ∠ O:B:A = ∟ := by
  euclid_intros
  euclid_apply InscribedAngleTheorem_opposingSides A B C O AB Ω
  euclid_apply isoTriangle_imp_eq_angles O A B
  euclid_apply triangle_angles_sum O A B
  euclid_finish

theorem LawOfSines_radius: ∀ (A B C O: Point), Triangle A B C ∧ Circumcentre O A B C → |(B─C)| = 2 * Real.sin (∠B:A:C) * |(A─O)| := by
  euclid_intros
  euclid_apply line_from_points B C as BC
  euclid_apply isoTriangle_base_side_cos O B C
  euclid_apply circle_from_points O A as Ω
  by_cases O.sameSide A BC
  · have h1: ∠O:C:B = ∟ - ∠B:A:C := by
      euclid_apply circumcentre_inscribedAngle_comp B C A O BC Ω
      euclid_finish
    have h2: |(B─C)| = 2 * |(A─O)| * cos (∠O:C:B) := by
      euclid_apply isoTriangle_base_side_cos O C B
      euclid_finish
    rw [h2, h1]
    euclid_apply rightAngle_eq_pi_div_two
    euclid_apply Real.cos_pi_div_two_sub (∠B:A:C)
    euclid_finish
  · by_cases O.opposingSides A BC
    · have h1: ∠O:C:B + ∟ =  ∠B:A:C := by
        euclid_apply circumcentre_inscribedAngle_diff_rightAngle B C A O BC Ω
        euclid_finish
      have h2: |(B─C)| = 2 * |(A─O)| * cos (∠O:C:B) := by
        euclid_apply isoTriangle_base_side_cos O C B
        euclid_finish
      rw [h2, ← h1]
      euclid_apply rightAngle_eq_pi_div_two
      euclid_apply Real.sin_add_pi_div_two (∠O:C:B)
      euclid_finish
    · euclid_assert MidPoint B O C
      euclid_apply ThalesTheorem B C A O Ω
      euclid_apply sin_pi_div_two
      euclid_apply rightAngle_eq_pi_div_two
      euclid_finish

end LeanGeo
