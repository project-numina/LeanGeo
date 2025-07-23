import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Basic.Perpendicular
import LeanGeo.Theorem.Circle.Basic
import LeanGeo.Theorem.Circle.Position
import LeanGeo.Theorem.Circle.Relation
import Book

open Elements.Book1
set_option maxHeartbeats 0
namespace LeanGeo

theorem radicalAxis_perp_lineOfCenters : ∀ (O₁ O₂ : Point) (L M: Line) (Ω₁ Ω₂ : Circle), O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ distinctPointsOnLine O₁ O₂ L ∧ RadicalAxis Ω₁ Ω₂ M → PerpLine L M := by
    euclid_intros
    euclid_apply line_nonempty M as A
    euclid_apply exists_distincts_points_on_line M A as B
    euclid_apply perpLine_if_eq_sq_diff A B O₁ O₂ M L
    euclid_finish

theorem radicalAxis_unique : ∀ (O₁ O₂ : Point) (L₁ L₂ : Line) (Ω₁ Ω₂ : Circle), O₁ ≠ O₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ RadicalAxis Ω₁ Ω₂ L₁ ∧ RadicalAxis Ω₁ Ω₂ L₂ → L₁ = L₂ := by
    euclid_intros
    euclid_apply line_from_points O₁ O₂ as M
    euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ M L₁ Ω₁ Ω₂
    euclid_apply intersection_lines L₁ M as C
    euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ M L₂ Ω₁ Ω₂
    euclid_apply intersection_lines L₂ M as R
    euclid_apply sq_diff_unique_onLine O₁ O₂ C R M
    by_contra
    euclid_apply perpLine_imp_rightAngleLine_parallel L₁ L₂ M
    euclid_finish

theorem radicalAxis_imp_neq_centres : ∀ (O₁ O₂ : Point) (L : Line) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ RadicalAxis Ω₁ Ω₂ L → O₁ ≠ O₂ := by
  euclid_intros
  by_contra
  euclid_apply line_nonempty L as P
  euclid_apply rad_gt_zero
  euclid_apply exists_point_on_circle
  euclid_finish

theorem exists_radicalAxis_lemma_1 :  ∀ (O₁ O₂: Point) (Ω₁ Ω₂ : Circle), O₁ ≠ O₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ → ∃ (P Q R S O: Point) (Ω : Circle), CirclesIntersectAtTwoPoints Ω Ω₁ P Q ∧ CirclesIntersectAtTwoPoints Ω Ω₂ R S ∧ O.isCentre Ω ∧ ¬ Coll O O₁ O₂:= by
    euclid_intros
    euclid_apply line_from_points O₁ O₂ as L
    euclid_apply exists_point_on_circle Ω₁ as A
    euclid_apply exists_point_on_circle Ω₂ as B
    euclid_apply extend_point_longer L O₁ O₂ O₂ B as C
    euclid_apply extend_point_longer L O₁ C O₁ A as D
    euclid_apply exists_perpBisector O₁ O₂ as M
    euclid_apply circle_from_points O₁ D as Ω'
    euclid_apply exists_midpoint O₁ O₂ as E
    have h_0 : E.onLine M := by
      euclid_apply perpBisector_iff O₁ O₂ M
      euclid_finish
    euclid_apply intersections_circle_line Ω' M as (O, F)
    euclid_apply circle_from_points O O₁ as Ω
    have h_1 : Ω.intersectsCircle Ω₁ := by
      euclid_apply point_on_circle_onlyif_to_rad O₁ O Ω
      euclid_apply rad_gt_zero Ω₁
      euclid_apply intersectCircles_if O O₁ Ω Ω₁
      euclid_finish
    have h_2 : Ω.intersectsCircle Ω₂ := by
      euclid_apply point_on_circle_onlyif_to_rad O₂ O Ω
      euclid_apply rad_gt_zero Ω₁
      euclid_apply intersectCircles_if O O₂ Ω Ω₂
      euclid_finish
    euclid_apply circles_intersect_at_two_points Ω Ω₁ as (P, Q)
    euclid_apply circles_intersect_at_two_points Ω Ω₂ as (R, S)
    euclid_finish

theorem exists_radicalAxis_lemma_2 : ∀ (O₁ O₂: Point) (Ω₁ Ω₂ : Circle), O₁ ≠ O₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ → ∃ (T : Point), Pow(T, Ω₁) = Pow(T, Ω₂) := by
    euclid_intros
    euclid_apply exists_radicalAxis_lemma_1 O₁ O₂ Ω₁ Ω₂ as (P, Q, R, S, O, Ω)
    euclid_apply line_from_points P Q as PQ
    euclid_apply line_from_points R S as RS
    have h_0 : PQ.intersectsLine RS := by
      by_contra
      euclid_apply line_from_points O O₁ as L₁
      euclid_apply line_from_points O O₂ as L₂
      have h_1 : PerpLine PQ L₁:= by
        euclid_apply intersectCircles_perpBisector_lineOfCentres O O₁ P Q L₁ Ω Ω₁
        euclid_apply perpBisector_iff P Q L₁
        euclid_finish
      have h_2 : PerpLine RS L₂ := by
        euclid_apply intersectCircles_perpBisector_lineOfCentres O O₂ R S L₂ Ω Ω₂
        euclid_apply perpBisector_iff R S L₂
        euclid_finish
      have h_3 : PerpLine L₂ PQ := by
        euclid_apply perp_parallel_imp_perp RS L₂ PQ
        euclid_finish
      euclid_apply perpLine_imp_rightAngleLine_parallel L₁ L₂ PQ
      euclid_finish
    by_cases PQ = RS
    · euclid_apply circle_points_between
      euclid_finish
    · euclid_apply intersection_lines PQ RS as T
      by_cases (P = R ∨ P = S) ∨ (Q = R ∨ Q = S)
      · euclid_apply point_on_circle_onlyif_to_pow
        euclid_finish
      · euclid_apply IntersectingSecantsAndChordsTheorem P Q R S T
        euclid_apply chord_intesectsCircle P Q PQ Ω₁
        euclid_apply chord_intesectsCircle R S RS Ω₂
        by_cases T.insideCircle Ω₁
        · have h_4 : T.insideCircle Ω₂ := by
            euclid_apply circle_line_intersections T R S
            euclid_finish
          euclid_apply pow_of_point_in_circle' T P Q PQ Ω₁
          euclid_apply pow_of_point_in_circle' T R S RS Ω₂
          euclid_finish
        · have h_4 : T.outsideCircle Ω₂ := by
            euclid_apply circle_points_extend
            euclid_finish
          euclid_apply pow_of_point_out_circle' T P Q PQ Ω₁
          euclid_apply pow_of_point_out_circle' T R S RS Ω₂
          euclid_finish

theorem exists_radicalAxis : ∀ (O₁ O₂: Point) (Ω₁ Ω₂ : Circle), O₁ ≠ O₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ → ∃ (L : Line), RadicalAxis Ω₁ Ω₂ L := by
    euclid_intros
    euclid_apply line_from_points O₁ O₂ as M
    euclid_apply exists_radicalAxis_lemma_2 O₁ O₂ Ω₁ Ω₂ as T
    euclid_apply exists_perpLine T M as LT
    have tmp : ∀ (A : Point), A.onLine LT → Pow(A, Ω₁) = Pow(A, Ω₂) := by
      euclid_intros
      by_cases A = T
      · euclid_finish
      · euclid_apply perpLine_imp_eq_sq_diff O₁ O₂ T A M LT
        euclid_finish
    use LT

theorem intersectCircles_radicalAxis : ∀ (P Q : Point) (PQ : Line) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ P Q ∧ distinctPointsOnLine P Q PQ → RadicalAxis Ω₁ Ω₂ PQ := by
    euclid_intros
    have h : Coll A P Q := by euclid_finish
    rcases h with h1|h2|h3|h4|h5
    · euclid_apply chord_intesectsCircle
      euclid_apply pow_of_point_out_circle' A P Q PQ Ω₁
      euclid_apply pow_of_point_out_circle' A P Q PQ Ω₂
      euclid_finish
    · euclid_apply chord_intesectsCircle
      euclid_apply pow_of_point_out_circle' A P Q PQ Ω₁
      euclid_apply pow_of_point_out_circle' A P Q PQ Ω₂
      euclid_finish
    · euclid_apply pow_of_point_in_circle' A P Q PQ Ω₁
      euclid_apply pow_of_point_in_circle' A P Q PQ Ω₂
      euclid_finish
    · euclid_apply point_on_circle_onlyif_to_pow A Ω₁
      euclid_apply point_on_circle_onlyif_to_pow A Ω₂
      euclid_finish
    · euclid_apply point_on_circle_onlyif_to_pow A Ω₁
      euclid_apply point_on_circle_onlyif_to_pow A Ω₂
      euclid_finish

theorem tangentCirclesInterior_radicalAxis : ∀ (P O₁ O₂ : Point) (L : Line) (Ω₁ Ω₂ : Circle), TangentCirclesInterior Ω₁ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ P.onCircle Ω₁ ∧ P.onCircle Ω₂ ∧(TangentLineCircleAtPoint P O₁ L Ω₁ ∨ TangentLineCircleAtPoint P O₂ L Ω₂) → RadicalAxis Ω₁ Ω₂ L := by
    euclid_intros
    euclid_apply exists_centre Ω₂ as O₂
    have h_0 : O₁ ≠ O₂ := by
      euclid_apply exists_point_on_circle Ω₁ as F
      euclid_apply exists_distinct_point_on_circle Ω₂ F as G
      euclid_finish
    euclid_apply line_from_points O₁ O₂ as M
    euclid_apply tangentCircles_coll_centres_tangentPoint P O₁ O₂ L Ω₁ Ω₂
    have h_1 : Pow(P, Ω₁) = Pow(P, Ω₂) := by
      euclid_apply point_on_circle_onlyif_to_pow
      euclid_finish
    by_cases A = P
    · euclid_finish
    · euclid_apply perpLine_imp_eq_sq_diff A P O₁ O₂ L
      euclid_finish

theorem radicalAxis_sameSide_if_pow_same_sign_lemma :∀ (O₁ O₂ P Q : Point) (L M: Line) (Ω₁ Ω₂ : Circle), RadicalAxis Ω₁ Ω₂ L ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ distinctPointsOnLine O₁ O₂ M ∧ P.onLine M ∧ Q.onLine M ∧ Pow(P, Ω₁) > Pow(P, Ω₂) ∧ Pow(Q, Ω₁) > Pow(Q, Ω₂) → P.sameSide Q L := by
  euclid_intros
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ M L Ω₁ Ω₂
  euclid_apply intersection_lines L M as A
  have h_1 : P = Q ∨ between P Q A ∨ between Q P A := by
    by_cases |(Q─O₁)| * |(Q─O₁)| - |(Q─O₂)| * |(Q─O₂)| > |(P─O₁)| * |(P─O₁)| - |(P─O₂)| * |(P─O₂)|
    · euclid_apply sq_diff_mono_distinctThreePointsOnLine O₁ O₂ A P Q M
      euclid_finish
    · by_cases |(Q─O₁)| * |(Q─O₁)| - |(Q─O₂)| * |(Q─O₂)| = |(P─O₁)| * |(P─O₁)| - |(P─O₂)| * |(P─O₂)|
      · euclid_apply sq_diff_mono_distinctTwoPointsOnLine
        euclid_finish
      · euclid_apply sq_diff_mono_distinctThreePointsOnLine O₁ O₂ A Q P M
        euclid_finish
  euclid_finish

theorem radicalAxis_sameSide_if_pow_same_sign : ∀ (P Q : Point) (L : Line) (Ω₁ Ω₂ : Circle), RadicalAxis Ω₁ Ω₂ L ∧ ((Pow(P, Ω₁) > Pow(P, Ω₂) ∧ Pow(Q, Ω₁) > Pow(Q, Ω₂)) ∨ (Pow(P, Ω₁) < Pow(P, Ω₂) ∧ Pow(Q, Ω₁) < Pow(Q, Ω₂))) → P.sameSide Q L := by
  euclid_intros
  euclid_apply exists_centre Ω₁ as O₁
  euclid_apply exists_centre Ω₂ as O₂
  have h_0 : O₁ ≠ O₂ := by
    euclid_apply radicalAxis_imp_neq_centres O₁ O₂ L Ω₁ Ω₂
    euclid_finish
  euclid_apply line_from_points O₁ O₂ as M
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ M L Ω₁ Ω₂
  euclid_apply intersection_lines L M as A
  by_cases P.onLine M
  · by_cases Q.onLine M
    · rcases right with h1|h2
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₁ O₂ P Q L M Ω₁ Ω₂
        euclid_finish
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₂ O₁ P Q L M Ω₂ Ω₁
        euclid_finish
    · euclid_apply exists_foot Q M as Q'
      euclid_apply line_from_points Q Q' as LQ
      have h_1 : PerpLine LQ M := by euclid_finish
      euclid_apply perpLine_imp_eq_sq_diff O₁ O₂ Q Q' M LQ
      have h_2 : ¬ LQ.intersectsLine L := by
        euclid_apply perpLine_imp_rightAngleLine_parallel L LQ M
        euclid_finish
      rcases right with h1|h2
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₁ O₂ P Q' L M Ω₁ Ω₂
        euclid_finish
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₂ O₁ P Q' L M Ω₂ Ω₁
        euclid_finish
  · euclid_apply exists_foot P M as P'
    euclid_apply line_from_points P P' as LP
    have h_1 : PerpLine LP M := by euclid_finish
    euclid_apply perpLine_imp_eq_sq_diff O₁ O₂ P P' M LP
    have h_2 : ¬ LP.intersectsLine L := by
      euclid_apply perpLine_imp_rightAngleLine_parallel L LP M
      euclid_finish
    by_cases Q.onLine M
    · rcases right with h1|h2
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₁ O₂ P' Q L M Ω₁ Ω₂
        euclid_finish
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₂ O₁ P' Q L M Ω₂ Ω₁
        euclid_finish
    · euclid_apply exists_foot Q M as Q'
      euclid_apply line_from_points Q Q' as LQ
      have h_1 : PerpLine LQ M := by euclid_finish
      euclid_apply perpLine_imp_eq_sq_diff O₁ O₂ Q Q' M LQ
      have h_2 : ¬ LQ.intersectsLine L := by
        euclid_apply perpLine_imp_rightAngleLine_parallel L LQ M
        euclid_finish
      rcases right with h1|h2
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₁ O₂ P' Q' L M Ω₁ Ω₂
        euclid_finish
      · euclid_apply radicalAxis_sameSide_if_pow_same_sign_lemma O₂ O₁ P' Q' L M Ω₂ Ω₁
        euclid_finish

theorem radicalAxis_opposingSides_if_pow_opposite_sign_lemma :∀ (O₁ O₂ P Q : Point) (L M: Line) (Ω₁ Ω₂ : Circle), RadicalAxis Ω₁ Ω₂ L ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ distinctPointsOnLine O₁ O₂ M ∧ P.onLine M ∧ Q.onLine M ∧ ((Pow(P, Ω₁) > Pow(P, Ω₂) ∧ Pow(Q, Ω₁) < Pow(Q, Ω₂)) ∨ (Pow(P, Ω₁) < Pow(P, Ω₂) ∧ Pow(Q, Ω₁) > Pow(Q, Ω₂))) → P.opposingSides Q L := by
  euclid_intros
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ M L Ω₁ Ω₂
  euclid_apply intersection_lines L M as A
  have h_0 : (Pow(P, Ω₁) > Pow(P, Ω₂) ∧ Pow(Q, Ω₁) < Pow(Q, Ω₂)) ∨ (Pow(P, Ω₁) < Pow(P, Ω₂) ∧ Pow(Q, Ω₁) > Pow(Q, Ω₂)) := by euclid_finish
  have h_1 : between P A Q := by
    rcases h_0 with h1|h2
    · euclid_apply sq_diff_mono_distinctThreePointsOnLine O₁ O₂ Q A P M
      euclid_finish
    · euclid_apply sq_diff_mono_distinctThreePointsOnLine O₁ O₂ P A Q M
      euclid_finish
  euclid_finish

theorem radicalAxis_opposingSides_if_pow_opposite_sign : ∀ (P Q : Point) (L : Line) (Ω₁ Ω₂ : Circle), RadicalAxis Ω₁ Ω₂ L ∧ ((Pow(P, Ω₁) > Pow(P, Ω₂) ∧ Pow(Q, Ω₁) < Pow(Q, Ω₂)) ∨ (Pow(P, Ω₁) < Pow(P, Ω₂) ∧ Pow(Q, Ω₁) > Pow(Q, Ω₂))) → P.opposingSides Q L := by
  euclid_intros
  euclid_apply exists_centre Ω₁ as O₁
  euclid_apply exists_centre Ω₂ as O₂
  have h_0 : O₁ ≠ O₂ := by
    euclid_apply radicalAxis_imp_neq_centres O₁ O₂ L Ω₁ Ω₂
    euclid_finish
  euclid_apply line_from_points O₁ O₂ as M
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ M L Ω₁ Ω₂
  euclid_apply intersection_lines L M as A
  by_cases P.onLine M
  · by_cases Q.onLine M
    · euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign_lemma O₁ O₂ P Q L M Ω₁ Ω₂
      euclid_finish
    · euclid_apply exists_foot Q M as Q'
      euclid_apply line_from_points Q Q' as LQ
      have h_1 : PerpLine LQ M := by euclid_finish
      euclid_apply perpLine_imp_eq_sq_diff O₁ O₂ Q Q' M LQ
      have h_2 : ¬ LQ.intersectsLine L := by
        euclid_apply perpLine_imp_rightAngleLine_parallel L LQ M
        euclid_finish
      euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign_lemma O₁ O₂ P Q' L M Ω₁ Ω₂
      euclid_finish
  · euclid_apply exists_foot P M as P'
    euclid_apply line_from_points P P' as LP
    have h_1 : PerpLine LP M := by euclid_finish
    euclid_apply perpLine_imp_eq_sq_diff O₁ O₂ P P' M LP
    have h_2 : ¬ LP.intersectsLine L := by
      euclid_apply perpLine_imp_rightAngleLine_parallel L LP M
      euclid_finish
    by_cases Q.onLine M
    · euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign_lemma O₁ O₂ P' Q L M Ω₁ Ω₂
      euclid_finish
    · euclid_apply exists_foot Q M as Q'
      euclid_apply line_from_points Q Q' as LQ
      have h_1 : PerpLine LQ M := by euclid_finish
      euclid_apply perpLine_imp_eq_sq_diff O₁ O₂ Q Q' M LQ
      have h_2 : ¬ LQ.intersectsLine L := by
        euclid_apply perpLine_imp_rightAngleLine_parallel L LQ M
        euclid_finish
      euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign_lemma O₁ O₂ P' Q' L M Ω₁ Ω₂
      euclid_finish

end LeanGeo
