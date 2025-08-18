import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Circle.Basic
import LeanGeo.Theorem.Circle.Position
import Book

open Elements.Book1
set_option maxHeartbeats 0
namespace LeanGeo

theorem intersectsCircle_imp_neq_centres : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ Ω₁ ≠ Ω₂ ∧ Ω₁.intersectsCircle Ω₂ → O₁ ≠ O₂ := by
    euclid_intros
    euclid_apply intersection_circles Ω₁ Ω₂ as P
    euclid_finish

theorem chord_intesectsCircle : ∀ (A B : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB → AB.intersectsCircle Ω := by
    euclid_intros
    euclid_apply exists_point_between_points_on_line AB A B as C
    euclid_finish

theorem circles_intersect_at_two_points : ∀ (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ Ω₁.intersectsCircle Ω₂ → ∃ (A B : Point), A ≠ B ∧ A.onCircle Ω₁ ∧ A.onCircle Ω₂ ∧ B.onCircle Ω₁ ∧ B.onCircle Ω₂ := by
    euclid_intros
    euclid_apply exists_centre Ω₁ as O₁
    euclid_apply exists_centre Ω₂ as O₂
    euclid_apply intersectsCircle_imp_neq_centres O₁ O₂ Ω₁ Ω₂
    euclid_apply line_from_points O₁ O₂ as L
    euclid_apply exists_point_not_on_line L as A
    euclid_apply intersection_opposite_side Ω₁ Ω₂ A O₁ O₂ L as B
    euclid_apply intersection_same_side Ω₁ Ω₂ A O₁ O₂ L as C
    euclid_finish

theorem circumcentre_isCentre_circumcircle : ∀ (a b c o : Point) (C : Circle), Triangle a b c ∧ a.onCircle C ∧ b.onCircle C ∧ c.onCircle C ∧ |(o─a)| = |(o─b)| ∧ |(o─b)| = |(o─c)| → o.isCentre C := by
  euclid_intros
  euclid_apply exists_centre C as w
  euclid_apply point_on_circle_onlyif w a b C
  euclid_apply point_on_circle_onlyif w b c C
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  by_contra
  euclid_apply line_from_points o w as OW
  euclid_apply perpBisector_if_eq_dist a b o w OW
  euclid_apply perpBisector_if_eq_dist b c o w OW
  have h1 : PerpLine AB OW := by
    euclid_apply perpBisector_iff a b OW
    euclid_finish
  have h2 : PerpLine BC OW := by
    euclid_apply perpBisector_iff b c OW
    euclid_finish
  have h3 : ¬ AB.intersectsLine BC := by
    euclid_apply perpLine_imp_rightAngleLine_parallel AB BC OW
    euclid_finish
  euclid_finish

theorem circles_intersect_le_two_points : ∀ (A B C : Point) (Ω₁ Ω₂ : Circle), A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ A.onCircle Ω₁ ∧ A.onCircle Ω₂ ∧ B.onCircle Ω₁ ∧ B.onCircle Ω₂ ∧ C.onCircle Ω₁ ∧ C.onCircle Ω₂ → Ω₁ = Ω₂ := by
    euclid_intros
    euclid_apply exists_centre Ω₁ as O₁
    euclid_apply exists_centre Ω₂ as O₂
    euclid_apply circumcentre_isCentre_circumcircle A B C O₂ Ω₁
    euclid_finish

theorem intersectCircles_if : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle),
O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ |(O₁─O₂)| < (rad Ω₁) + (rad Ω₂) ∧ (rad Ω₂) + |(O₁─O₂)| > (rad Ω₁) ∧ (rad Ω₁) + |(O₁─O₂)| > (rad Ω₂) → Ω₁.intersectsCircle Ω₂ := by
    euclid_intros
    have h_0 : O₁ ≠ O₂ := by
        euclid_finish
    euclid_apply line_from_points O₁ O₂ as L
    euclid_apply intersections_circle_line Ω₁ L as (P, Q)
    have tmp : between P O₁ Q := by
        euclid_finish
    by_cases between P O₁ O₂
    · have h_1 : P.outsideCircle Ω₂ := by
        euclid_apply point_out_circle_if_to_rad P O₂ Ω₂
        euclid_finish
      have h_2 : Q.insideCircle Ω₂ := by
        euclid_apply point_in_circle_if_to_rad Q O₂ Ω₂
        euclid_finish
      euclid_finish
    · have h_1 : Q.outsideCircle Ω₂ := by
        euclid_apply point_out_circle_if_to_rad Q O₂ Ω₂
        euclid_finish
      have h_2 : P.insideCircle Ω₂ := by
        euclid_apply point_in_circle_if_to_rad P O₂ Ω₂
        euclid_finish
      euclid_finish

theorem intersectCircles_onlyif : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle),
Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ Ω₁.intersectsCircle Ω₂ → |(O₁─O₂)| < (rad Ω₁) + (rad Ω₂) ∧ (rad Ω₂) + |(O₁─O₂)| > (rad Ω₁) ∧ (rad Ω₁) + |(O₁─O₂)| > (rad Ω₂) := by
    euclid_intros
    euclid_apply intersectsCircle_imp_neq_centres O₁ O₂ Ω₁ Ω₂
    euclid_apply line_from_points O₁ O₂ as L
    euclid_apply intersection_circles Ω₁ Ω₂ as P
    by_cases P.onLine L
    · euclid_apply exists_point_not_on_line L as Q
      euclid_apply intersection_same_side Ω₁ Ω₂ Q O₁ O₂ L as R
      euclid_apply triangle_inequality O₁ O₂ R
      euclid_apply triangle_inequality O₂ R O₁
      euclid_apply triangle_inequality R O₁ O₂
      euclid_finish
    · euclid_apply triangle_inequality O₁ O₂ P
      euclid_apply triangle_inequality O₂ P O₁
      euclid_apply triangle_inequality P O₁ O₂
      euclid_finish

theorem intersectsCircle_symm : ∀ (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ Ω₁.intersectsCircle Ω₂ → Ω₂.intersectsCircle Ω₁ := by
  euclid_intros
  euclid_apply exists_centre Ω₁ as O₁
  euclid_apply exists_centre Ω₂ as O₂
  euclid_apply intersectCircles_onlyif O₁ O₂ Ω₁ Ω₂
  euclid_apply intersectCircles_if O₂ O₁ Ω₂ Ω₁
  euclid_finish

theorem separateCircles_onlyif : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ SeperateCircles Ω₁ Ω₂ → |(O₁─O₂)| > (rad Ω₁) + (rad Ω₂) := by
  euclid_intros
  by_cases |(O₁─O₂)| ≥ (rad Ω₁)
  · euclid_apply exists_point_on_circle Ω₁ as A
    euclid_apply line_from_points A O₁ as L
    euclid_apply line_from_points O₁ O₂ as M
    euclid_apply proposition_3 O₁ O₂ O₁ A M L as B
    euclid_apply point_out_circle_onlyif_to_rad B O₂ Ω₂
    euclid_finish
  · euclid_apply point_in_circle_if_to_rad O₂ O₁ Ω₁
    euclid_finish

theorem separateCircles_if : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ |(O₁─O₂)| > (rad Ω₁) + (rad Ω₂) → SeperateCircles Ω₁ Ω₂ := by
  euclid_intros
  have h_0 : O₁ ≠ O₂ := by
    euclid_apply rad_gt_zero
    euclid_finish
  euclid_apply line_from_points O₁ O₂ as L
  by_cases P.onLine L
  · by_cases P.insideCircle Ω₁
    · euclid_apply point_in_circle_onlyif_to_rad P O₁ Ω₁
      by_cases P.insideCircle Ω₂
      · euclid_apply point_in_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish
      · euclid_apply point_on_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish
    · euclid_apply point_on_circle_onlyif_to_rad P O₁ Ω₁
      by_cases P.insideCircle Ω₂
      · euclid_apply point_in_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish
      · euclid_apply point_on_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish
  · euclid_apply triangle_inequality O₁ O₂ P
    by_cases P.insideCircle Ω₁
    · euclid_apply point_in_circle_onlyif_to_rad P O₁ Ω₁
      by_cases P.insideCircle Ω₂
      · euclid_apply point_in_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish
      · euclid_apply point_on_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish
    · euclid_apply point_on_circle_onlyif_to_rad P O₁ Ω₁
      by_cases P.insideCircle Ω₂
      · euclid_apply point_in_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish
      · euclid_apply point_on_circle_onlyif_to_rad P O₂ Ω₂
        euclid_finish

theorem tangentCirclesExterior_onlyif : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ TangentCirclesExterior Ω₁ Ω₂ → |(O₁─O₂)| = (rad Ω₁) + (rad Ω₂) := by
    euclid_intros
    simp at right_1
    euclid_apply right_1 as A
    euclid_apply line_from_points O₁ O₂ as L
    by_cases A.onLine L
    · euclid_finish
    · euclid_apply triangle_inequality O₁ O₂ A
      euclid_apply triangle_inequality A O₁ O₂
      euclid_apply triangle_inequality A O₂ O₁
      have h : Ω₁ ≠ Ω₂ := by euclid_finish
      euclid_apply intersectCircles_if O₁ O₂ Ω₁ Ω₂
      euclid_apply circles_intersect_at_two_points Ω₁ Ω₂ as (B, C)
      euclid_finish

theorem tangentCirclesExterior_if : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ |(O₁─O₂)| = (rad Ω₁) + (rad Ω₂) → TangentCirclesExterior Ω₁ Ω₂ := by
    euclid_intros
    have h_0 : O₁ ≠ O₂ := by
      euclid_apply rad_gt_zero
      euclid_finish
    euclid_apply line_from_points O₁ O₂ as L
    euclid_apply rad_gt_zero Ω₂
    euclid_apply point_out_circle_if_to_rad O₂ O₁ Ω₁
    euclid_apply intersection_circle_line_between_points Ω₁ L O₁ O₂ as A
    euclid_apply point_on_circle_if_to_rad A O₂ Ω₂
    have h_1 : (∀ (B : Point), ¬B = A → B.onCircle Ω₁ → ¬B.onCircle Ω₂) := by
      euclid_intros
      euclid_apply triangle_inequality O₁ O₂ B
      euclid_finish
    have h_2 : ∀ (C : Point), C.insideCircle Ω₁ ∧ C.insideCircle Ω₂ → False := by
      euclid_intros
      by_cases C.onLine L
      · euclid_finish
      · euclid_apply triangle_inequality O₁ O₂ C
        euclid_finish
    euclid_finish

theorem tangentCirclesInterior_onlyif : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ TangentCirclesInterior Ω₁ Ω₂ → |(O₁─O₂)| = (rad Ω₂) - (rad Ω₁) := by
    euclid_intros
    simp at right_1
    euclid_apply right_1 as A
    have h_0 : O₁ ≠ O₂ := by
      euclid_apply exists_distinct_point_on_circle Ω₂ A as G
      euclid_finish
    euclid_apply line_from_points O₁ O₂ as L
    euclid_apply intersection_circle_line_extending_points Ω₂ L O₂ O₁ as P
    euclid_apply intersection_circle_line_extending_points Ω₂ L O₂ P as Q
    have h_1 : (rad Ω₂) > (rad Ω₁) := by
      euclid_apply intersection_circle_line_extending_points Ω₁ L O₁ O₂ as S
      euclid_finish
    by_cases A.onLine L
    · euclid_finish
    · euclid_apply triangle_inequality O₁ O₂ A
      euclid_apply triangle_inequality A O₁ O₂
      euclid_apply triangle_inequality A O₂ O₁
      have h : Ω₁ ≠ Ω₂ := by euclid_finish
      euclid_apply intersectCircles_if O₁ O₂ Ω₁ Ω₂
      euclid_apply circles_intersect_at_two_points Ω₁ Ω₂ as (B, C)
      euclid_finish

theorem tangentCirclesInterior_if : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ |(O₁─O₂)| = (rad Ω₂) - (rad Ω₁) → TangentCirclesInterior Ω₁ Ω₂:= by
    euclid_intros
    have h_0 : O₁ ≠ O₂ := by
      euclid_apply exists_point_on_circle Ω₁ as F
      euclid_apply exists_point_on_circle Ω₂ as G
      euclid_finish
    euclid_apply line_from_points O₁ O₂ as L
    euclid_apply rad_gt_zero Ω₁
    euclid_apply point_in_circle_if_to_rad O₁ O₂ Ω₂
    euclid_apply intersection_circle_line_extending_points Ω₂ L O₁ O₂ as A
    have h_1 : A.onCircle Ω₁ := by
      euclid_apply point_on_circle_if_to_rad A O₁ Ω₁
      euclid_finish
    have h_2 : ∀ (B : Point), ¬B = A → B.onCircle Ω₁ → ¬B.onCircle Ω₂ := by
      euclid_intros
      euclid_apply triangle_inequality B O₂ O₁
      euclid_finish
    have h_3 : ∀ (C : Point), C.insideCircle Ω₁ → C.insideCircle Ω₂ := by
      euclid_intros
      by_cases C.onLine L
      · euclid_finish
      · euclid_apply triangle_inequality C O₂ O₁
        euclid_finish
    euclid_finish

theorem insideCircle_onlyif : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ InsideCircle Ω₁ Ω₂ → |(O₁─O₂)| < (rad Ω₂) - (rad Ω₁) := by
    euclid_intros
    by_cases |(O₁─O₂)| < (rad Ω₂)
    · euclid_apply exists_point_on_circle Ω₁ as A
      euclid_apply line_from_points A O₁ as L
      by_cases O₁ = O₂
      · euclid_apply exists_point_on_circle Ω₁ as B
        euclid_apply point_in_circle_onlyif_to_rad B O₂ Ω₂
        euclid_finish
      · euclid_apply line_from_points O₁ O₂ as M
        euclid_apply intersection_circle_line_extending_points Ω₁ M O₁ O₂ as B
        euclid_apply point_in_circle_onlyif_to_rad B O₂ Ω₂
        euclid_finish
    · euclid_apply point_in_circle_onlyif_to_rad O₁ O₂ Ω₂
      euclid_finish

theorem insideCircle_if : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ |(O₁─O₂)| < (rad Ω₂) - (rad Ω₁) → InsideCircle Ω₁ Ω₂ := by
    euclid_intros
    have h_0 : Ω₁ ≠ Ω₂ := by euclid_finish
    have h_1 : |(P─O₁)| ≤ (rad Ω₁) := by
      by_cases P.insideCircle Ω₁
      · euclid_apply point_in_circle_onlyif_to_rad P O₁ Ω₁
        euclid_finish
      · euclid_apply point_on_circle_onlyif_to_rad P O₁ Ω₁
        euclid_finish
    by_cases O₁ = O₂
    · euclid_apply point_in_circle_if_to_rad P O₂ Ω₂
      euclid_finish
    · euclid_apply line_from_points O₁ O₂ as L
      have h_2 : |(P─O₂)| ≤ |(P─O₁)| + |(O₂─O₁)| := by
        by_cases P.onLine L
        · euclid_finish
        · euclid_apply triangle_inequality P O₂ O₁
          euclid_finish
      euclid_apply point_in_circle_if_to_rad P O₂ Ω₂
      euclid_finish

theorem tangentCircles_def : ∀ (Ω₁ Ω₂ : Circle), TangentCircles Ω₁ Ω₂ → TangentCirclesInterior Ω₁ Ω₂ ∨ TangentCirclesInterior Ω₂ Ω₁ ∨ TangentCirclesExterior Ω₁ Ω₂ := by
    euclid_intros
    euclid_apply exists_centre Ω₁ as O₁
    euclid_apply exists_centre Ω₂ as O₂
    have h : ∃ A, A.onCircle Ω₁ ∧ A.onCircle Ω₂ ∧ ∀ (B : Point), ¬B = A → B.onCircle Ω₁ → ¬B.onCircle Ω₂ := by euclid_finish
    euclid_apply h as A
    by_cases O₁ = O₂
    · euclid_finish
    · euclid_apply line_from_points O₁ O₂ as L
      by_cases A.onLine L
      · have h_0 : |(O₁─O₂)| = (rad Ω₂) + (rad Ω₁) ∨ |(O₁─O₂)| = (rad Ω₂) - (rad Ω₁) ∨ |(O₁─O₂)| = (rad Ω₁) - (rad Ω₂) := by euclid_finish
        rcases h_0 with h1|h2|h3
        · euclid_apply tangentCirclesExterior_if O₁ O₂ Ω₁ Ω₂
          euclid_finish
        · euclid_apply tangentCirclesInterior_if O₁ O₂ Ω₁ Ω₂
          euclid_finish
        · euclid_apply tangentCirclesInterior_if O₂ O₁ Ω₂ Ω₁
          euclid_finish
      · euclid_apply triangle_inequality A O₁ O₂
        euclid_apply triangle_inequality A O₂ O₁
        euclid_apply triangle_inequality O₁ O₂ A
        euclid_apply intersectCircles_if O₁ O₂ Ω₁ Ω₂
        euclid_apply circles_intersect_at_two_points Ω₁ Ω₂ as (B, C)
        euclid_finish

theorem tangentCircles_onlyif : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ TangentCircles Ω₁ Ω₂ → |(O₁─O₂)| = (rad Ω₂) + (rad Ω₁) ∨ |(O₁─O₂)| = (rad Ω₂) - (rad Ω₁) ∨ |(O₁─O₂)| = (rad Ω₁) - (rad Ω₂) := by
    euclid_intros
    euclid_apply tangentCircles_def Ω₁ Ω₂
    rcases h with h1|h2|h3
    · euclid_apply tangentCirclesInterior_onlyif O₁ O₂ Ω₁ Ω₂
      euclid_finish
    · euclid_apply tangentCirclesInterior_onlyif O₂ O₁ Ω₂ Ω₁
      euclid_finish
    · euclid_apply tangentCirclesExterior_onlyif O₁ O₂ Ω₁ Ω₂
      euclid_finish

theorem tangentCircles_if : ∀ (O₁ O₂ : Point) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ (|(O₁─O₂)| = (rad Ω₂) + (rad Ω₁) ∨ |(O₁─O₂)| = (rad Ω₂) - (rad Ω₁) ∨ |(O₁─O₂)| = (rad Ω₁) - (rad Ω₂)) → TangentCircles Ω₁ Ω₂ := by
    euclid_intros
    rcases right_2 with h1|h2|h3
    · euclid_apply tangentCirclesExterior_if O₁ O₂ Ω₁ Ω₂
      euclid_finish
    · euclid_apply tangentCirclesInterior_if O₁ O₂ Ω₁ Ω₂
      euclid_finish
    · euclid_apply tangentCirclesInterior_if O₂ O₁ Ω₂ Ω₁
      euclid_finish

theorem circles_position_classification : ∀ (Ω₁ Ω₂ : Circle), Ω₁ = Ω₂ ∨ Ω₁.intersectsCircle Ω₂ ∨ TangentCircles Ω₁ Ω₂ ∨ SeperateCircles Ω₁ Ω₂ ∨ InsideCircle Ω₁ Ω₂ ∨ InsideCircle Ω₂ Ω₁ := by
    euclid_intros
    euclid_apply exists_centre Ω₁ as O₁
    euclid_apply exists_centre Ω₂ as O₂
    by_cases Ω₁ ≠ Ω₂
    · have h : |(O₁─O₂)| < (rad Ω₁) - (rad Ω₂) ∨ |(O₁─O₂)| < (rad Ω₂) - (rad Ω₁) ∨ |(O₁─O₂)| > (rad Ω₂) + (rad Ω₁) ∨ (|(O₁─O₂)| = (rad Ω₁) - (rad Ω₂) ∨ |(O₁─O₂)| = (rad Ω₂) - (rad Ω₁) ∨ |(O₁─O₂)| = (rad Ω₂) + (rad Ω₁)) ∨ (|(O₁─O₂)| > (rad Ω₁) - (rad Ω₂) ∧ |(O₁─O₂)| > (rad Ω₂) - (rad Ω₁) ∧ |(O₁─O₂)| < (rad Ω₂) + (rad Ω₁)) := by euclid_finish
      rcases h with h1|h2|h3|h4|h5
      · euclid_apply insideCircle_if O₂ O₁ Ω₂ Ω₁
        euclid_finish
      · euclid_apply insideCircle_if O₁ O₂ Ω₁ Ω₂
        euclid_finish
      · euclid_apply separateCircles_if O₁ O₂ Ω₁ Ω₂
        euclid_finish
      · euclid_apply tangentCircles_if O₁ O₂ Ω₁ Ω₂
        euclid_finish
      · euclid_apply intersectCircles_if O₁ O₂ Ω₁ Ω₂
        euclid_finish
    · euclid_finish

theorem tangentLine_or_intersectsCircle_if_common_point : ∀ (A O: Point) (L : Line) (Ω : Circle), O.isCentre Ω ∧ A.onLine L ∧ A.onCircle Ω → TangentLineCircleAtPoint A O L Ω ∨ L.intersectsCircle Ω := by
  euclid_intros
  by_cases O.onLine L
  · euclid_finish
  · obtain ⟨B, Hb⟩ := exists_foot O L (by euclid_finish)
    by_cases A = B
    · euclid_finish
    · have tmp : |(B─O)| < |(A─O)| := by
        euclid_apply line_from_points A O as AO
        euclid_apply line_from_points B O as BO
        euclid_apply PythagoreanTheorem B A O L AO BO
        euclid_finish
      euclid_finish

theorem circles_position_classification_with_common_points : ∀ (A : Point) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ A.onCircle Ω₁ ∧ A.onCircle Ω₂ → TangentCircles Ω₁ Ω₂ ∨ Ω₁.intersectsCircle Ω₂ := by
  euclid_intros
  euclid_apply exists_centre Ω₁ as O₁
  euclid_apply exists_centre Ω₂ as O₂
  euclid_apply line_from_points O₁ O₂ as L
  by_cases A.onLine L
  · euclid_apply tangentCircles_if O₁ O₂ Ω₁ Ω₂
    euclid_finish
  · euclid_apply triangle_inequality A O₁ O₂
    euclid_apply triangle_inequality O₁ O₂ A
    euclid_apply triangle_inequality O₂ A O₁
    euclid_apply intersectCircles_if O₁ O₂ Ω₁ Ω₂
    euclid_finish

theorem tangentCircles_coll_centres_tangentPoint : ∀ (P O₁ O₂ : Point) (L : Line) (Ω₁ Ω₂ : Circle), TangentCircles Ω₁ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ P.onCircle Ω₁ ∧ P.onCircle Ω₂ → Coll O₁ P O₂ := by
    euclid_intros
    euclid_apply tangentCircles_def Ω₁ Ω₂
    rcases h with h1|h2|h3
    · euclid_apply tangentCirclesInterior_onlyif O₁ O₂ Ω₁ Ω₂
      euclid_apply triangle_inequality
      euclid_finish
    · euclid_apply tangentCirclesInterior_onlyif O₂ O₁ Ω₂ Ω₁
      euclid_apply triangle_inequality
      euclid_finish
    · euclid_apply tangentCirclesExterior_onlyif O₁ O₂ Ω₁ Ω₂
      euclid_apply triangle_inequality
      euclid_finish

theorem tangentCircles_commonTangent : ∀ (P O₁ O₂ : Point) (L : Line) (Ω₁ Ω₂ : Circle), TangentCircles Ω₁ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ P.onCircle Ω₁ ∧ P.onCircle Ω₂ ∧ (TangentLineCircleAtPoint P O₁ L Ω₁ ∨ TangentLineCircleAtPoint P O₂ L Ω₂) → (TangentLineCircleAtPoint P O₁ L Ω₁ ∧ TangentLineCircleAtPoint P O₂ L Ω₂) := by
    euclid_intros
    have h_0 : O₁ ≠ O₂ := by
      euclid_apply exists_point_on_circle Ω₁ as F
      euclid_apply exists_distinct_point_on_circle Ω₂ F as G
      euclid_finish
    euclid_apply line_from_points O₁ O₂ as M
    euclid_apply tangentCircles_coll_centres_tangentPoint P O₁ O₂ L Ω₁ Ω₂
    euclid_finish

theorem intersectCircles_perpBisector_lineOfCentres :
  ∀  (O1 O2 A B : Point) (L : Line)(C1 C2 : Circle),
  (CirclesIntersectAtTwoPoints C1 C2 A B) ∧ O1.isCentre C1 ∧ O2.isCentre C2 ∧ O1 ≠ O2
  ∧ (O1.onLine L)
  ∧ (O2.onLine L)
  → PerpBisector A B L :=
by
  euclid_intros
  euclid_apply perpBisector_if_eq_dist A B O1 O2 L
  euclid_finish

theorem intersectCircles_lineOfCentres_triangle: ∀ (O1 O2 A B : Point) (C1 C2: Circle), O1 ≠ O2 ∧ O1.isCentre C1 ∧ O2.isCentre C2∧ CirclesIntersectAtTwoPoints C1 C2 A B →  Triangle O1 O2 A := by
  euclid_intros
  euclid_apply line_from_points O1 O2 as L
  euclid_apply intersectCircles_perpBisector_lineOfCentres O1 O2 A B L C1 C2
  euclid_finish

end LeanGeo
