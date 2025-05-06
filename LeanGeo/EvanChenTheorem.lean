import SystemE
import LeanGeo

namespace LeanGeo

--Lemma 1.3 (Self-full angle). If A, B, C are distinct points, then ∠A:O:C + ∠ C:O:B + ∠ B:O:A = ∟ + ∟ +  ∟ + ∟.
theorem self_fullAngle : ∀ (A B C O : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ insideTriangle O A B C AB BC CA → ∠A:O:C + ∠ C:O:B + ∠ B:O:A = ∟ + ∟ +  ∟ + ∟ := by
  euclid_intros
  euclid_apply triangle_angleSum A O B
  euclid_apply triangle_angleSum C O B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum A B C
  euclid_finish

--Theorem 1.3 (Inscribed Angle Theorem). If ∠A C B is inscribed in a circle, then it subtends an arc with measure 2∠A C B.
--Draw in O C. Set α = ∠A C O and β = ∠B C O, and let θ = α + β. Because A O = C O we have ∠O A C = ∠O C A = α, so ∠A O C = 180° − 2α. Similarly ∠B O C = 180° − 2β. Hence ∠A O B = 360° − [(180° − 2α) + (180° − 2β)] = 2θ.
theorem inscribed_angle_theorem :
  ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (insideTriangle O A B C AB BC CA) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_apply self_fullAngle A B C O AB BC CA
  euclid_apply line_from_points O C as OC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O A as OA
  euclid_apply isoTriangle_eqAngle O A C
  euclid_apply isoTriangle_eqAngle O C B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum C O B
  euclid_finish

theorem inside_triangle_opposingsides :  ∀ (A B C I : Point) (AB BC CA BI : Line), (formTriangle A B C AB BC CA) ∧ (insideTriangle I A B C AB BC CA) ∧ (distinctPointsOnLine B I BI) → A.opposingSides C BI := by
  euclid_intros
  euclid_finish


theorem opposingsides_inside_triangle :  ∀ (A B C I : Point) (AB BC CA AI BI CI : Line), (formTriangle A B C AB BC CA) ∧ (distinctPointsOnLine B I BI) ∧ (distinctPointsOnLine C I CI) ∧ A.opposingSides C BI ∧ B.opposingSides C AI → insideTriangle I A B C AB BC CA:= by
  euclid_intros
  sorry

theorem angleBisector_opposingsides : ∀ (A B C I : Point) (AI : Line), (distinctPointsOnLine A I AI)∧ triangle A B C ∧ ∠ I:A:B = ∠ I:A:C →  B.opposingSides C AI := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_finish


theorem incenter_inside : ∀ (A B C I : Point) (AB BC CA : Line), (formTriangle A B C AB BC CA) ∧ (inCentre I A B C) → insideTriangle I A B C AB BC CA := by
  euclid_intros
  euclid_apply line_from_points A I as AI
  euclid_apply line_from_points B I as BI
  euclid_apply line_from_points C I as CI
  euclid_apply angleBisector_opposingsides A B C I AI
  euclid_apply angleBisector_opposingsides C A B I CI
  euclid_apply angleBisector_opposingsides B C A I BI
  euclid_apply opposingsides_inside_triangle A B C I AB BC CA AI BI CI
  euclid_finish

--Example 1.4. If I is the incenter of ΔA B C then ∠B I C = 90° + ½A.
--原则：让题面叙述变得简单？
theorem incenter_angle : ∀ (A B C I : Point), (triangle A B C) ∧ (inCentre I A B C) → ∠B:I:C = ∟ + ∠B:A:C / 2 := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A C as CA
  euclid_apply line_from_points B C as BC
  --euclid_assert formTriangle A B C AB BC CA
  euclid_apply incenter_inside A B C I AB BC CA
  --euclid_apply self_fullAngle A B C I AB BC CA
  euclid_apply triangle_angleSum I B C
  euclid_apply triangle_angleSum A B C
  --euclid_assert ∠A:B:C = 2 * ∠I:B:C
  --euclid_assert ∠A:C:B = 2 * ∠I:C:B
  euclid_finish
