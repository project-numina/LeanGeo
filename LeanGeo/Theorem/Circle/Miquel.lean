import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Circle.RadicalAxis
import LeanGeo.Theorem.Circle.Cyclic
import Book

open Elements.Book1
set_option maxHeartbeats 0
namespace LeanGeo

theorem intersectCircles_similarTriangles_of_one_secant_lemma_1 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ B.outsideCircle Ω₂ ∧ ∠K:O₁:O₂ < ∟ → ∠K:B:C = ∠K:O₁:O₂ := by
  euclid_intros
  euclid_apply line_from_points A B as M
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O₁ O₂ as L
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  euclid_apply intersectCircles_radicalAxis A K AK Ω₁ Ω₂
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ L AK Ω₁ Ω₂
  euclid_apply intersection_lines AK L as W
  have h_1 : Pow(O₁, Ω₁) < Pow(O₁, Ω₂) := by
    euclid_apply PythagoreanTheorem_to_acuteAngle O₁ K O₂
    euclid_finish
  have h_2 : B.sameSide O₁ AK := by
    euclid_apply point_out_circle_onlyif_to_pow B Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply radicalAxis_sameSide_if_pow_same_sign B O₁ AK Ω₁ Ω₂
    euclid_finish
  euclid_apply InscribedAngleTheorem_sameSide A K B O₁ AK Ω₁
  euclid_apply intersectCircles_perpBisector_lineOfCentres O₁ O₂ A K L Ω₁ Ω₂
  euclid_apply congruentTriangles_SSS A O₁ O₂ K O₁ O₂
  have h_3 : ∠A:O₁:K = ∠A:O₁:O₂ + ∠K:O₁:O₂ := by
    euclid_apply between_imp_angles_sum O₁ A W K
    euclid_apply line_from_points O₁ K as LK
    euclid_apply line_from_points O₁ A as LA
    have h_4 : LiesOnRay O₁ O₂ W := by
      by_contra
      euclid_apply proposition_17 K W O₁ AK L LK
      by_cases W = O₁
      · euclid_finish
      · euclid_apply coll_supp_angles K W O₁ O₂
        euclid_finish
    euclid_apply equal_angles O₁ K K W O₂ LK L
    euclid_apply equal_angles O₁ A A W O₂ LA L
    euclid_finish
  euclid_apply line_from_points B K as BK
  euclid_apply equal_angles B K K A C BK M
  euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant_lemma_2 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ B.outsideCircle Ω₂ ∧ ∠K:O₁:O₂ > ∟ → ∠K:B:C = ∠K:O₁:O₂ := by
  euclid_intros
  euclid_apply line_from_points A B as M
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O₁ O₂ as L
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  euclid_apply intersectCircles_radicalAxis A K AK Ω₁ Ω₂
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ L AK Ω₁ Ω₂
  euclid_apply intersection_lines AK L as W
  have h_1 : Pow(O₁, Ω₁) > Pow(O₁, Ω₂) := by
    euclid_apply PythagoreanTheorem_to_obtuseAngle O₁ K O₂
    euclid_finish
  have h_2 : B.opposingSides O₁ AK := by
    euclid_apply point_out_circle_onlyif_to_pow B Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign B O₁ AK Ω₁ Ω₂
    euclid_finish
  euclid_apply InscribedAngleTheorem_opposingSides A K B O₁ AK Ω₁
  euclid_apply intersectCircles_perpBisector_lineOfCentres O₁ O₂ A K L Ω₁ Ω₂
  euclid_apply congruentTriangles_SSS A O₁ O₂ K O₁ O₂
  have h_3 : ∠A:O₁:K + ∠A:O₁:O₂ + ∠K:O₁:O₂ = ∟ + ∟ + ∟ + ∟ := by
    euclid_apply line_from_points O₁ K as LK
    euclid_apply line_from_points O₁ A as LA
    have h_4 : between W O₁ O₂ := by
      euclid_apply proposition_17 K W O₁ AK L LK
      euclid_finish
    euclid_apply between_imp_angles_sum O₁ A W K
    euclid_apply coll_supp_angles K W O₁ O₂
    euclid_apply coll_supp_angles A W O₁ O₂
    euclid_finish
  euclid_apply line_from_points B K as BK
  euclid_apply equal_angles B K K A C BK M
  euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant_lemma_3 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ C ≠ A ∧ B.insideCircle Ω₂ ∧ ∠K:O₁:O₂ < ∟ → ∠K:B:C = ∠K:O₁:O₂ := by
  euclid_intros
  euclid_apply line_from_points A B as M
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O₁ O₂ as L
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  euclid_apply intersectCircles_radicalAxis A K AK Ω₁ Ω₂
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ L AK Ω₁ Ω₂
  euclid_apply intersection_lines AK L as W
  have h_1 : Pow(O₁, Ω₁) < Pow(O₁, Ω₂) := by
    euclid_apply PythagoreanTheorem_to_acuteAngle O₁ K O₂
    euclid_finish
  have h_2 : B.opposingSides O₁ AK := by
    euclid_apply point_in_circle_onlyif_to_pow B Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign B O₁ AK Ω₁ Ω₂
    euclid_finish
  euclid_apply InscribedAngleTheorem_opposingSides A K B O₁ AK Ω₁
  euclid_apply intersectCircles_perpBisector_lineOfCentres O₁ O₂ A K L Ω₁ Ω₂
  euclid_apply congruentTriangles_SSS A O₁ O₂ K O₁ O₂
  have h_3 : ∠A:O₁:K = ∠A:O₁:O₂ + ∠K:O₁:O₂ := by
    euclid_apply between_imp_angles_sum O₁ A W K
    euclid_apply line_from_points O₁ K as LK
    euclid_apply line_from_points O₁ A as LA
    have h_4 : LiesOnRay O₁ O₂ W := by
      by_contra
      euclid_apply proposition_17 K W O₁ AK L LK
      by_cases W = O₁
      · euclid_finish
      · euclid_apply coll_supp_angles K W O₁ O₂
        euclid_finish
    euclid_apply equal_angles O₁ K K W O₂ LK L
    euclid_apply equal_angles O₁ A A W O₂ LA L
    euclid_finish
  euclid_apply line_from_points B K as BK
  euclid_apply coll_supp_angles K A B C
  euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant_lemma_4 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ C ≠ A ∧ B.insideCircle Ω₂ ∧ ∠K:O₁:O₂ > ∟ → ∠K:B:C = ∠K:O₁:O₂ := by
  euclid_intros
  euclid_apply line_from_points A B as M
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O₁ O₂ as L
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  euclid_apply intersectCircles_radicalAxis A K AK Ω₁ Ω₂
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ L AK Ω₁ Ω₂
  euclid_apply intersection_lines AK L as W
  have h_1 : Pow(O₁, Ω₁) > Pow(O₁, Ω₂) := by
    euclid_apply PythagoreanTheorem_to_obtuseAngle O₁ K O₂
    euclid_finish
  have h_2 : B.sameSide O₁ AK := by
    euclid_apply point_in_circle_onlyif_to_pow B Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply radicalAxis_sameSide_if_pow_same_sign B O₁ AK Ω₁ Ω₂
    euclid_finish
  euclid_apply InscribedAngleTheorem_sameSide A K B O₁ AK Ω₁
  euclid_apply intersectCircles_perpBisector_lineOfCentres O₁ O₂ A K L Ω₁ Ω₂
  euclid_apply congruentTriangles_SSS A O₁ O₂ K O₁ O₂
  have h_3 : ∠A:O₁:K + ∠A:O₁:O₂ + ∠K:O₁:O₂ = ∟ + ∟ + ∟ + ∟ := by
    euclid_apply line_from_points O₁ K as LK
    euclid_apply line_from_points O₁ A as LA
    have h_4 : between W O₁ O₂ := by
      euclid_apply proposition_17 K W O₁ AK L LK
      euclid_finish
    euclid_apply between_imp_angles_sum O₁ A W K
    euclid_apply coll_supp_angles K W O₁ O₂
    euclid_apply coll_supp_angles A W O₁ O₂
    euclid_finish
  euclid_apply line_from_points B K as BK
  euclid_apply coll_supp_angles K A B C
  euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant_lemma_5 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ B ≠ A ∧ B ≠ K ∧ ∠K:O₁:O₂ = ∟ → ∠K:B:C = ∠K:O₁:O₂ := by
  euclid_intros
  euclid_apply line_from_points A B as M
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O₁ O₂ as L
  euclid_apply intersectCircles_perpBisector_lineOfCentres O₁ O₂ A K L Ω₁ Ω₂
  euclid_apply congruentTriangles_SSS A O₁ O₂ K O₁ O₂
  have h_1 : O₁.onLine AK := by
    euclid_apply coll_if_supp_angles O₂ O₁ A K L
    euclid_finish
  euclid_apply ThalesTheorem A K B O₁ Ω₁
  euclid_apply line_from_points B K as BK
  by_cases B.insideCircle Ω₂
  · by_cases A = C
    · euclid_finish
    · euclid_apply coll_supp_angles K A B C
      euclid_finish
  · have h_2 : B.outsideCircle Ω₂ := by
      euclid_apply circles_intersect_le_two_points
      euclid_finish
    euclid_apply equal_angles B K K A C BK M
    euclid_finish



theorem intersectCircles_similarTriangles_of_one_secant_subcase_1 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ between B A C ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ B ≠ K ∧ C ≠ K → SimilarTriangles O₁ O₂ K B C K := by
  euclid_intros
  euclid_apply intersectsCircle_symm Ω₁ Ω₂
  have h : B ≠ C := by
      by_contra
      by_cases B = K
      · euclid_finish
      · euclid_apply circles_intersect_le_two_points B K A Ω₁ Ω₂
        euclid_finish
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  have h_0 : ∠K:O₁:O₂ = ∠K:B:C := by
    have h_1 : ∠K:O₁:O₂ < ∟ ∨ ∠K:O₁:O₂ = ∟ ∨ ∠K:O₁:O₂ > ∟ := by euclid_finish
    rcases h_1 with h1|h2|h3
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_1 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_5 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_2 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
  have h_2 : ∠K:O₂:O₁ = ∠K:C:B := by
    have h_3 : ∠K:O₂:O₁ < ∟ ∨ ∠K:O₂:O₁ = ∟ ∨ ∠K:O₂:O₁ > ∟ := by euclid_finish
    rcases h_3 with h1|h2|h3
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_1 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_5 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_2 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
  have h_3 :¬ Coll B C K := by
    euclid_apply line_from_points A B as L
    euclid_finish
  euclid_apply similar_AA O₁ O₂ K B C K
  euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant_subcase_2 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ between A B C ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ B ≠ K ∧ C ≠ K → SimilarTriangles O₁ O₂ K B C K := by
  euclid_intros
  euclid_apply intersectsCircle_symm Ω₁ Ω₂
  have h : B ≠ C := by
      by_contra
      by_cases B = K
      · euclid_finish
      · euclid_apply circles_intersect_le_two_points B K A Ω₁ Ω₂
        euclid_finish
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  have h_0 : ∠K:O₁:O₂ = ∠K:B:C := by
    have h_1 : ∠K:O₁:O₂ < ∟ ∨ ∠K:O₁:O₂ = ∟ ∨ ∠K:O₁:O₂ > ∟ := by euclid_finish
    rcases h_1 with h1|h2|h3
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_3 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_5 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_4 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
  have h_2 : ∠K:O₂:O₁ = ∠K:C:B := by
    have h_3 : ∠K:O₂:O₁ < ∟ ∨ ∠K:O₂:O₁ = ∟ ∨ ∠K:O₂:O₁ > ∟ := by euclid_finish
    rcases h_3 with h1|h2|h3
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_1 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_5 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_2 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
  have h_3 :¬ Coll B C K := by
    euclid_apply line_from_points A B as L
    euclid_finish
  euclid_apply similar_AA O₁ O₂ K B C K
  euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant_subcase_3 : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ between B C A ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ B ≠ K ∧ C ≠ K → SimilarTriangles O₁ O₂ K B C K := by
  euclid_intros
  euclid_apply intersectsCircle_symm Ω₁ Ω₂
  have h : B ≠ C := by
      by_contra
      by_cases B = K
      · euclid_finish
      · euclid_apply circles_intersect_le_two_points B K A Ω₁ Ω₂
        euclid_finish
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  have h_0 : ∠K:O₁:O₂ = ∠K:B:C := by
    have h_1 : ∠K:O₁:O₂ < ∟ ∨ ∠K:O₁:O₂ = ∟ ∨ ∠K:O₁:O₂ > ∟ := by euclid_finish
    rcases h_1 with h1|h2|h3
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_1 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_5 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_2 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
  have h_2 : ∠K:O₂:O₁ = ∠K:C:B := by
    have h_3 : ∠K:O₂:O₁ < ∟ ∨ ∠K:O₂:O₁ = ∟ ∨ ∠K:O₂:O₁ > ∟ := by euclid_finish
    rcases h_3 with h1|h2|h3
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_3 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_5 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_lemma_4 O₂ O₁ A C B K Ω₂ Ω₁
      euclid_finish
  have h_3 :¬ Coll B C K := by
    euclid_apply line_from_points A B as L
    euclid_finish
  euclid_apply similar_AA O₁ O₂ K B C K
  euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ K ∧ C ≠ K → SimilarTriangles O₁ O₂ K B C K := by
    euclid_intros
    have h_0 : O₁ ≠ O₂ := by
      euclid_apply intersectsCircle_imp_neq_centres O₁ O₂ Ω₁ Ω₂
      euclid_finish
    have h_1 : B ≠ C := by
      by_contra
      by_cases B = K
      · euclid_finish
      · euclid_apply circles_intersect_le_two_points B K A Ω₁ Ω₂
        euclid_finish
    have h_2 : between A B C ∨ between B A C ∨ between A C B := by euclid_finish
    rcases h_2 with h1|h2|h3
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_subcase_2 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_subcase_1 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish
    · euclid_apply intersectCircles_similarTriangles_of_one_secant_subcase_3 O₁ O₂ A B C K Ω₁ Ω₂
      euclid_finish

theorem intersectCircles_similarTriangles_of_one_secant' : ∀ (O₁ O₂ A B C K : Point) (Ω₁ Ω₂: Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ K ∧ C ≠ K ∧ (¬ Coll B O₁ K ∧ ¬ Coll C O₂ K) → SimilarTriangles O₁ B K O₂ C K := by
  euclid_intros
  euclid_apply intersectCircles_similarTriangles_of_one_secant O₁ O₂ A B C K Ω₁ Ω₂
  euclid_apply similar_SSS O₁ B K O₂ C K
  euclid_finish

theorem intersectCircles_eq_angles_of_two_secants_lemma_1 : ∀ (O₁ O₂ A B D K : Point) (AK : Line) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ distinctPointsOnLine A K AK ∧ B.onCircle Ω₁ ∧ B ≠ A ∧ B ≠ K ∧ D.onCircle Ω₁ ∧ D ≠ A ∧ D ≠ K ∧ ((B.insideCircle Ω₂ ∧ D.insideCircle Ω₂) ∨ (B.outsideCircle Ω₂ ∧ D.outsideCircle Ω₂)) → ∠B:K:D = ∠B:A:D := by
  euclid_intros
  euclid_apply line_from_points A B as L₁
  euclid_apply line_from_points A D as L₂
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O₁ O₂ as L
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  euclid_apply intersectCircles_radicalAxis A K AK Ω₁ Ω₂
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ L AK Ω₁ Ω₂
  by_cases B.outsideCircle Ω₂
  · euclid_apply point_out_circle_onlyif_to_pow B Ω₂
    euclid_apply point_out_circle_onlyif_to_pow D Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply point_on_circle_onlyif_to_pow D Ω₁
    euclid_apply radicalAxis_sameSide_if_pow_same_sign B D AK Ω₁ Ω₂
    euclid_apply cyclic_eq_angles' A K B D AK Ω₁
    euclid_finish
  · euclid_apply point_in_circle_onlyif_to_pow B Ω₂
    euclid_apply point_in_circle_onlyif_to_pow D Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply point_on_circle_onlyif_to_pow D Ω₁
    euclid_apply radicalAxis_sameSide_if_pow_same_sign B D AK Ω₁ Ω₂
    euclid_apply cyclic_eq_angles' A K B D AK Ω₁
    euclid_finish

theorem intersectCircles_eq_angles_of_two_secants_lemma_2 : ∀ (O₁ O₂ A B D K : Point) (AK : Line) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ distinctPointsOnLine A K AK ∧ B.onCircle Ω₁ ∧ B ≠ A ∧ B ≠ K ∧ D.onCircle Ω₁ ∧ D ≠ A ∧ D ≠ K ∧ ((B.insideCircle Ω₂ ∧ D.outsideCircle Ω₂) ∨ (B.outsideCircle Ω₂ ∧ D.insideCircle Ω₂)) → ∠B:K:D + ∠B:A:D = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points A B as L₁
  euclid_apply line_from_points A D as L₂
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O₁ O₂ as L
  euclid_apply intersectCircles_lineOfCentres_triangle O₁ O₂ K A Ω₁ Ω₂
  euclid_apply intersectCircles_radicalAxis A K AK Ω₁ Ω₂
  euclid_apply radicalAxis_perp_lineOfCenters O₁ O₂ L AK Ω₁ Ω₂
  by_cases B.outsideCircle Ω₂
  · euclid_apply point_out_circle_onlyif_to_pow B Ω₂
    euclid_apply point_in_circle_onlyif_to_pow D Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply point_on_circle_onlyif_to_pow D Ω₁
    euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign B D AK Ω₁ Ω₂
    euclid_apply cyclic_supp_angles' A K B D AK Ω₁
    euclid_finish
  · euclid_apply point_in_circle_onlyif_to_pow B Ω₂
    euclid_apply point_out_circle_onlyif_to_pow D Ω₂
    euclid_apply point_on_circle_onlyif_to_pow B Ω₁
    euclid_apply point_on_circle_onlyif_to_pow D Ω₁
    euclid_apply radicalAxis_opposingSides_if_pow_opposite_sign B D AK Ω₁ Ω₂
    euclid_apply cyclic_supp_angles' A K B D AK Ω₁
    euclid_finish

theorem intersectCircles_eq_angles_of_two_secants : ∀ (O₁ O₂ A B C D E K : Point) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ K ∧ C ≠ K ∧ D.onCircle Ω₁ ∧ E.onCircle Ω₂ ∧ Coll A D E ∧ A ≠ D ∧ A ≠ E ∧ D ≠ K ∧ E ≠ K → ∠B:K:D = ∠C:K:E := by
  euclid_intros
  have h_0 : O₁ ≠ O₂ := by
    euclid_apply intersectsCircle_imp_neq_centres O₁ O₂ Ω₁ Ω₂
    euclid_finish
  have h_1 : B ≠ C := by
    by_contra
    by_cases B = K
    · euclid_finish
    · euclid_apply circles_intersect_le_two_points B K A Ω₁ Ω₂
      euclid_finish
  have h_2 : D ≠ E := by
    by_contra
    by_cases D = K
    · euclid_finish
    · euclid_apply circles_intersect_le_two_points D K A Ω₁ Ω₂
      euclid_finish
  have h_3 : between B A C ∨ between A B C ∨ between A C B := by euclid_finish
  have h_4 : between D A E ∨ between A D E ∨ between A E D := by euclid_finish
  euclid_apply intersectsCircle_symm Ω₁ Ω₂
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points A B as L₁
  euclid_apply line_from_points A D as L₂
  rcases h_3 with h1|h2|h3
  · rcases h_4 with h4|h5|h6
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply eq_opposite_angles
      euclid_finish
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply equal_angles A B B D E L₁ L₂
      euclid_apply coll_supp_angles D B A C
      euclid_finish
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply equal_angles A B B D E L₁ L₂
      euclid_apply coll_supp_angles D B A C
      euclid_finish
  · rcases h_4 with h4|h5|h6
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply equal_angles A B C D D L₁ L₂
      euclid_apply coll_supp_angles B D A E
      euclid_finish
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply eq_opposite_angles
      euclid_finish
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply eq_opposite_angles
      euclid_finish
  · rcases h_4 with h4|h5|h6
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply equal_angles A B C D D L₁ L₂
      euclid_apply coll_supp_angles B D A E
      euclid_finish
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_2 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply eq_opposite_angles
      euclid_finish
    · euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₁ O₂ A B D K AK Ω₁ Ω₂
      euclid_apply intersectCircles_eq_angles_of_two_secants_lemma_1 O₂ O₁ A C E K AK Ω₂ Ω₁
      euclid_apply eq_opposite_angles
      euclid_finish

theorem intersectCircles_similarTriangles_of_two_secants : ∀ (O₁ O₂ A B C D E K : Point) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ K ∧ C ≠ K ∧ D.onCircle Ω₁ ∧ E.onCircle Ω₂ ∧ Coll A D E ∧ A ≠ D ∧ A ≠ E ∧ D ≠ K ∧ E ≠ K → SimilarTriangles B C K D E K := by
  euclid_intros
  euclid_apply intersectCircles_similarTriangles_of_one_secant O₁ O₂ A B C K Ω₁ Ω₂
  euclid_apply intersectCircles_similarTriangles_of_one_secant O₁ O₂ A D E K Ω₁ Ω₂
  euclid_apply similarTriangles_trans B C K O₁ O₂ K D E K
  euclid_finish

theorem intersectCircles_similarTriangles_of_two_secants' : ∀ (O₁ O₂ A B C D E K : Point) (Ω₁ Ω₂ : Circle), Ω₁ ≠ Ω₂ ∧ O₁.isCentre Ω₁ ∧ O₂.isCentre Ω₂ ∧ CirclesIntersectAtTwoPoints Ω₁ Ω₂ A K ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ K ∧ C ≠ K ∧ D.onCircle Ω₁ ∧ E.onCircle Ω₂ ∧ Coll A D E ∧ A ≠ D ∧ A ≠ E ∧ D ≠ K ∧ E ≠ K ∧ (B ≠ D ∨ C ≠ E) → SimilarTriangles B D K C E K := by
  euclid_intros
  euclid_apply line_from_points A B as L₁
  euclid_apply line_from_points A D as L₂
  have h_0 : B ≠ D ∧ C ≠ E := by
    by_contra
    euclid_apply circle_points_between
    euclid_finish
  euclid_apply intersectCircles_similarTriangles_of_two_secants O₁ O₂ A B C D E K Ω₁ Ω₂
  euclid_apply intersectCircles_eq_angles_of_two_secants O₁ O₂ A B C D E K Ω₁ Ω₂
  euclid_apply similarTriangles_from_rotary_similarTriangles K B C D E
  euclid_finish

theorem Reim_to_tangentCirclesExterior : ∀ (A B C D E : Point) (BD CE : Line) (Ω₁ Ω₂ : Circle), TangentCirclesExterior Ω₁ Ω₂ ∧ A.onCircle Ω₁ ∧ A.onCircle Ω₂ ∧ B.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ Coll A B C ∧ A ≠ B ∧ A ≠ C ∧ D.onCircle Ω₁ ∧ E.onCircle Ω₂ ∧ Coll A D E ∧ A ≠ D ∧ A ≠ E ∧ distinctPointsOnLine B D BD ∧ distinctPointsOnLine C E CE → ¬ BD.intersectsLine CE := by
  euclid_intros
  euclid_apply exists_centre Ω₁ as O₁
  euclid_apply exists_centre Ω₂ as O₂
  euclid_apply line_from_points O₁ O₂ as L
  have h_0 : between O₁ A O₂ := by
    euclid_apply tangentCirclesExterior_onlyif O₁ O₂ Ω₁ Ω₂
    euclid_apply triangle_inequality
    euclid_finish
  euclid_apply proposition_11 O₁ O₂ A L as P
  euclid_apply line_from_points A P as M
  euclid_apply extend_point M P A as Q
  have h_1 : between B A C := by
    euclid_apply exists_midpoint A C as R₁
    euclid_apply exists_midpoint A B as R₂
    euclid_finish
  have h_2 : between D A E := by
    euclid_apply exists_midpoint A D as R₁
    euclid_apply exists_midpoint A E as R₂
    euclid_finish
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points D E as DE
  have h_3 : ∠D:B:C = ∠B:C:E := by
    by_cases D.sameSide P BC
    · euclid_apply AlternateSegmentTheorem A D B P O₁ Ω₁ DE BD BC M
      euclid_apply AlternateSegmentTheorem A E C Q O₂ Ω₂ DE CE BC M
      euclid_apply eq_opposite_angles D P A Q E
      euclid_finish
    · have h_4 : ¬ P.onLine BC  := by
        by_contra
        euclid_apply tangentLine_not_in_circle A B O₁ Ω₁
        euclid_finish
      euclid_apply AlternateSegmentTheorem A D B Q O₁ Ω₁ DE BD BC M
      euclid_apply AlternateSegmentTheorem A E C P O₂ Ω₂ DE CE BC M
      euclid_apply eq_opposite_angles D Q A P E
      euclid_finish
  euclid_apply parallel_if_eq_alternateAngles BD CE BC B C D E
  euclid_finish

theorem MiquelTheorem_lemma_1 : ∀ (A B C D E F P : Point) (ABC CDF BDE AEF : Line) (BCD DEF : Circle), CompleteQuadrilateral A B C D E F ABC CDF BDE AEF ∧ CirclesIntersectAtTwoPoints BCD DEF D P ∧ Circumcircle BCD B C D ∧ Circumcircle DEF D E F ∧ A.sameSide P BDE → A.sameSide P CDF := by
  euclid_intros
  by_contra
  euclid_apply line_from_points C P as CP
  euclid_apply line_from_points B P as BP
  euclid_apply cyclic_opposingSides_symm C D B P CDF BP BCD
  euclid_apply cyclic_opposingSides_imp_sameSide B D C P CP ABC BCD
  euclid_finish

theorem MiquelTheorem_lemma_2 : ∀ (A B C D E F P : Point) (ABC CDF BDE AEF : Line) (BCD DEF : Circle), CompleteQuadrilateral A B C D E F ABC CDF BDE AEF ∧ CirclesIntersectAtTwoPoints BCD DEF D P ∧ Circumcircle BCD B C D ∧ Circumcircle DEF D E F → A.opposingSides P BDE ∧ A.opposingSides P CDF := by
  euclid_intros
  by_contra
  have h : A.sameSide P BDE ∧ A.sameSide P CDF := by
    by_cases A.sameSide P BDE
    · euclid_apply MiquelTheorem_lemma_1 A B C D E F P ABC CDF BDE AEF BCD DEF
      euclid_finish
    · euclid_apply intersectsCircle_symm BCD DEF
      euclid_apply MiquelTheorem_lemma_1 A F E D C B P AEF BDE CDF ABC DEF BCD
      euclid_finish
  euclid_apply cyclic_opposingSides_imp_sameSide D P F E AEF CDF DEF
  euclid_apply cyclic_opposingSides_imp_sameSide D P B C ABC BDE BCD
  have h_0 : ∠P:E:A < ∠D:E:A := by euclid_finish
  have h_1 : ∠P:C:B < ∠D:C:A := by euclid_finish
  euclid_apply line_from_points F P as FP
  euclid_apply line_from_points B P as BP
  euclid_apply cyclic_eq_angles P F D E FP DEF
  euclid_apply cyclic_eq_angles P B D C BP BCD
  have h_2 : ∠B:D:F = ∠P:C:B + ∠P:E:F := by euclid_finish
  euclid_apply completeQuadrilateral_angles_sum A B C D E F ABC CDF BDE AEF
  euclid_apply eq_opposite_angles F B D E C
  euclid_finish

theorem MiquelTheorem_lemma_3 : ∀ (A B C D E F P : Point) (ABC CDF BDE AEF : Line) (BCD DEF ABE ACF : Circle), CompleteQuadrilateral A B C D E F ABC CDF BDE AEF ∧ Circumcircle BCD B C D ∧ Circumcircle DEF D E F ∧ Circumcircle ABE A B E ∧ Circumcircle ACF A C F ∧ CirclesIntersectAtTwoPoints BCD DEF D P → P.onCircle ABE := by
  euclid_intros
  euclid_apply exists_centre BCD as O₁
  euclid_apply exists_centre DEF as O₂
  euclid_apply intersectCircles_similarTriangles_of_two_secants' O₁ O₂ D B E C F P BCD DEF
  euclid_apply line_from_points A P as AP
  euclid_apply MiquelTheorem_lemma_2 A B C D E F P ABC CDF BDE AEF BCD DEF
  have h_2 : ∠E:P:B + ∠E:A:C = ∟ + ∟ := by
    euclid_apply cyclic_supp_angles D E F P BDE DEF
    euclid_apply cyclic_eq_angles B D C P BDE BCD
    euclid_apply between_imp_angles_sum P B D E
    euclid_apply coll_supp_angles D A F E
    euclid_apply triangle_angles_sum A C F
    euclid_finish
  euclid_apply cyclic_if_supp_angles E B A P BDE ABE
  euclid_finish

theorem MiquelTheorem : ∀ (A B C D E F : Point) (ABC CDF BDE AEF : Line) (BCD DEF ABE ACF : Circle), CompleteQuadrilateral A B C D E F ABC CDF BDE AEF ∧ Circumcircle BCD B C D ∧ Circumcircle DEF D E F ∧ Circumcircle ABE A B E ∧ Circumcircle ACF A C F → ∃ (P : Point), P.onCircle BCD ∧ P.onCircle DEF ∧ P.onCircle ABE ∧ P.onCircle ACF := by
  euclid_intros
  have h_0 : BCD.intersectsCircle DEF := by
    euclid_apply circles_position_classification_with_common_points D BCD DEF
    by_contra
    have h : TangentCirclesExterior DEF BCD ∨ TangentCirclesInterior DEF BCD ∨ TangentCirclesInterior BCD DEF := by euclid_finish
    rcases h with h1|h2|h3
    · euclid_apply Reim_to_tangentCirclesExterior D E B F C AEF ABC DEF BCD
      euclid_finish
    · euclid_apply exists_midpoint D E as T
      euclid_finish
    · euclid_apply exists_midpoint D C as T
      euclid_finish
  euclid_apply exists_centre BCD as O₁
  euclid_apply exists_centre DEF as O₂
  euclid_apply line_from_points O₁ O₂ as L
  have h_1 : ¬ D.onLine L := by
    euclid_apply point_on_circle_if_to_rad D O₁ BCD
    euclid_apply point_on_circle_if_to_rad D O₂ DEF
    euclid_apply intersectCircles_onlyif O₁ O₂ BCD DEF
    euclid_finish
  euclid_apply intersection_opposite_side BCD DEF D O₁ O₂ L as P
  euclid_apply intersectsCircle_symm BCD DEF
  euclid_apply MiquelTheorem_lemma_3 A B C D E F P ABC CDF BDE AEF BCD DEF ABE ACF
  euclid_apply MiquelTheorem_lemma_3 A F E D C B P AEF BDE CDF ABC DEF BCD ACF ABE
  euclid_finish

end LeanGeo
