import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library6: ∀ (A B C O: Point), triangle A B C ∧ circumCentre O A B C → |(B─C)| = 2 * Real.sin (∠B:A:C) * |(A─O)| := by
  euclid_intros
  euclid_apply line_from_points B C as BC
  euclid_apply isoTriangle_cos O B C
  euclid_apply circle_from_points O A as Ω
  by_cases O.sameSide A BC
  · have h1: ∠O:C:B = ∟ - ∠B:A:C := by
      euclid_apply circumcenter_inscribed_angle_sameSide B C A O BC Ω
      euclid_finish
    have h2: |(B─C)| = 2 * |(A─O)| * Real.cos (∠O:C:B) := by
      euclid_apply isoTriangle_cos O C B
      euclid_finish
    rw [h2, h1]
    euclid_apply rightAngle_eq_pi_div_two
    euclid_apply Real.cos_pi_div_two_sub (∠B:A:C)
    euclid_finish
  · by_cases O.opposingSides A BC
    · have h1: ∠O:C:B + ∟ =  ∠B:A:C := by
        euclid_apply circumcenter_inscribed_angle_opposingSides B C A O BC Ω
        euclid_finish
      have h2: |(B─C)| = 2 * |(A─O)| * Real.cos (∠O:C:B) := by
        euclid_apply isoTriangle_cos O C B
        euclid_finish
      rw [h2, ← h1]
      euclid_apply rightAngle_eq_pi_div_two
      euclid_apply Real.sin_add_pi_div_two (∠O:C:B)
      euclid_finish
    · euclid_assert midpoint B O C
      euclid_apply diameter_rightAngle B C A O Ω
      euclid_apply Real.sin_pi_div_two
      euclid_apply rightAngle_eq_pi_div_two
      euclid_finish
