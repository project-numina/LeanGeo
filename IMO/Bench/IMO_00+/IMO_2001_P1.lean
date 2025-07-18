import Mathlib
import SystemE
import LeanGeo
open LeanGeo Real
--Consider an acute-angled triangle $ABC$. Let $P$ be the foot of the altitude of triangle $ABC$ issuing from the vertex $A$, and let $O$ be the circumcenter of triangle $ABC$. Assume that $\angle C \geq \angle B+30^{\circ}$. Prove that $\angle A+\angle COP < 90^{\circ}$.
--To Trigonometry.lean
--To Triangle.lean
set_option maxHeartbeats 0
theorem sin_ineqaulity(B C : ℝ)
  (hB : 0 < B ∧ B < π) (hC : 0 < C ∧ C < π)
  (hC1 : C ≥ B + π/6) : 4 * sin B * cos C ≤ 1 := by
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC11, hC22⟩
  have h1 : cos C ≤ cos (B + π / 6) := by
    have h2 : C ≥ B + π / 6 := hC1
    have h3 : C < π := by linarith [hC22]
    have h4 : 0 < B + π / 6 := by
      linarith [hB1, Real.pi_pos]
    have h5 : B + π / 6 < π := by
      nlinarith [hB2, hC11, hC22, Real.pi_pos]
    have h6 : cos C ≤ cos (B + π / 6) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      all_goals
        nlinarith [Real.pi_pos, hB1, hB2, hC11, hC22, Real.pi_pos]
    linarith
  have h2 : sin B * cos (B + π / 6) ≤ 1 / 4 := by
    have h21 : cos (B + π / 6) = cos B * cos (π / 6) - sin B * sin (π / 6) := by
      rw [Real.cos_add]
    have h22 : cos (π / 6) = Real.sqrt 3 / 2 := by
      rw [cos_pi_div_six]
    have h23 : sin (π / 6) = 1 / 2 := by
      rw [sin_pi_div_six]
    have h24 : sin B * cos (B + π / 6) = (Real.sqrt 3 / 2) * sin B * cos B - (1 / 2) * sin B ^ 2 := by
      rw [h21, h22, h23]
      ring_nf
    have h25 : (Real.sqrt 3 / 2) * sin B * cos B - (1 / 2) * sin B ^ 2 ≤ 1 / 4 := by
      nlinarith [sq_nonneg (sin B - 1 / 2), sq_nonneg (cos B - Real.sqrt 3 / 2),
          sq_nonneg (sin B ^ 2 - 1 / 4), sq_nonneg (sin B - Real.sqrt 3 / 2),
          sq_nonneg (cos B ^ 2 - 1 / 4), sq_nonneg (cos B - 1 / 2),
          Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < (3 : ℝ)),
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith),
          Real.sin_sq_add_cos_sq B, mul_nonneg (show 0 ≤ (0 : ℝ) by linarith) (show 0 ≤ (0 : ℝ) by linarith),
          Real.sin_pos_of_pos_of_lt_pi hB1 (by linarith : B < Real.pi)]
    linarith [h24, h25]
  have h3 : 0 < sin B := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [hB1, hB2, Real.pi_pos]
  nlinarith [h1, h2, h3, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, Real.pi_pos]


theorem sin_range (A : ℝ) (hA : 0 < A ∧ A < π/2) : sin A < 1 ∧ sin A > 0 := by
  have h1 : 0 < A := hA.1
  have h2 : A < π / 2 := hA.2
  have h3 : sin A < 1 := by
    have h4 : sin (π / 2) = 1 := by
      rw [sin_pi_div_two]
    have h5 : sin A < sin (π / 2) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos, Real.pi_gt_three, h1, h2]
    linarith [h4, h5]
  have h6 : sin A > 0 := by
    have h7 : sin (0 : ℝ) = 0 := by
      simp [Real.sin_zero]
    have h8 : sin (0 : ℝ) < sin A := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos, Real.pi_gt_three, h1, h2]
    linarith [h7, h8]
  constructor
  · linarith [h3]
  · linarith [h6]
--To Triangle, Generated b


theorem IMO_2001_P1 :
  ∀ (A B C P O : Point) (AB BC CA : Line),
    formAcuteTriangle A B C AB BC CA ∧
    foot A P BC ∧
    circumCentre O A B C ∧
    ∠ A:C:B ≥ ∠ C:B:A + ∟/3 →
    ∠ B:A:C + ∠ C:O:P < ∟ := by
  euclid_intros
  euclid_apply rightAngle_eq_pi_div_two
  euclid_apply acute_triangle_circumCentre_inside A B C O AB BC CA
  euclid_apply circle_from_points O B as Ω
  euclid_apply circumcenter_inscribed_angle_complementary B C A O BC CA AB Ω
  have h0: 4 * sin (∠ B:A:C) * sin (∠A:B:C) * cos (∠A:C:B) < 1 := by
    have h1: 0 < ∠ A:B:C ∧ ∠ A:B:C < π := by
      euclid_finish
    have h2: 0 < ∠ A:C:B ∧ ∠ A:C:B < π := by
      euclid_finish
    have h3: (sin (∠ B:A:C) < 1) ∧ (sin (∠ B:A:C) > 0) := by
      euclid_apply sin_range (∠B:A:C)
      euclid_finish
    have h4: ∠ A:C:B ≥ ∠ C:B:A + π/6 := by
      euclid_finish
    have h5: 4 * sin (∠A:B:C) * cos (∠A:C:B) ≤ 1 := by
      euclid_apply sin_inequality (∠A:B:C) (∠A:C:B)
      euclid_finish
    nlinarith

  have h1: between B P C := by
    euclid_apply acute_triangle_foot_between A B C P BC
    euclid_finish
  have h2: |(P─C)| < |(P─O)| := by
    have h3: |(P─C)| * |(P─C)|  < |(P─O)| * |(P─O)| := by
      have h4: |(O─C)| * |(O─C)| - |(O─P)| * |(O─P)| = |(P─B)| * |(P─C)|:= by
        euclid_apply apollonius_on_isoceles O B C P BC
        euclid_finish
      have h5: |(P─C)| = |(A─C)| * cos (∠ A:C:P) := by
        euclid_apply rightTriangle_cos P C A
        euclid_finish
      have h6:  |(A─C)| = 2 * |(O─C)| * sin (∠A:B:C) := by
        euclid_apply law_of_sin_radius B A C O
        euclid_finish
      have h7:  |(B─C)| = 2 * |(O─C)| * sin (∠B:A:C) := by
        euclid_apply law_of_sin_radius A B C O
        euclid_finish
      have h8: ∠A:C:P = ∠A:C:B := by
        euclid_apply angle_between_transfer B P C A
        euclid_finish
      have h9: |(P─C)| * |(B─C)| < |(O─C)| * |(O─C)| := by
        rw [h5, h6, h7,h8]
        have h10: (|(O─C)| * |(O─C)|) > 0 := by euclid_finish
        calc
          _ = (4 * sin (∠ B:A:C) * sin (∠A:B:C) * cos (∠A:C:B)) * (|(O─C)| * |(O─C)|) := by linarith
          _ < 1 * (|(O─C)| * |(O─C)|) := by euclid_finish
          _ = _ := by euclid_finish
      euclid_finish
    euclid_assert |(P─C)| > 0
    euclid_assert |(P─O)| > 0
    nlinarith
  euclid_assert triangle O C P
  euclid_apply greater_side_greater_angle P C O
  have h_final: ∠ P:C:O = ∠ B:C:O := by
    euclid_apply angle_between_transfer B P C O
    euclid_finish
  euclid_finish
