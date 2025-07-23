import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Triangle.Basic

set_option maxHeartbeats 0
namespace LeanGeo

theorem perpLine_imp_rightAngle : ∀ (P Q R: Point) (L1 L2 : Line), PerpLine L1 L2 ∧ TwoLinesIntersectAtPoint L1 L2 P ∧ Q.onLine L1 ∧ R.onLine L2 ∧ Q ≠ P ∧ R ≠ P → ∠Q:P:R = ∟ := by
  euclid_intros
  euclid_finish

theorem foot_if_rightAngle: ∀ (A B C: Point) (l : Line), ¬ A.onLine l ∧ distinctPointsOnLine B C l ∧ ∠A:B:C = ∟ → Foot A B l:= by
  euclid_intros
  euclid_apply coll_angles_eq
  euclid_finish

theorem perpLine_unique : ∀ (A : Point) (L : Line),
  ¬(A.onLine L)
  → ∃! (M : Line),
    A.onLine M
    ∧ PerpLine L M
    :=
by
  intro A L hAL
  obtain ⟨A', hA'⟩ := exists_foot A L (by euclid_finish)
  obtain ⟨M, hM⟩ := line_from_points A A' (by euclid_finish)
  use M
  apply And.intro
  · euclid_finish
  · intro M' hM'
    suffices ∀ x : Point, x.onLine M' → x.onLine M by
      euclid_finish
    intro x hx
    -- M' is a line through A perpendicular to L. Let X be its intersection with L.
    obtain ⟨X, hX⟩ := hM'.2
    -- This setup implies that X is the Foot of the perpendicular from A to L.
    have h_foot_X: Foot A X L := by
      euclid_finish
    -- We already have A' as the Foot of the perpendicular from A to L.
    -- The Foot is unique, so X must be the same point as A'.
    have h_X_is_A': X = A' := by
      by_cases h_eq : X = A'
      · assumption
      · have h_neq : X ≠ A' := h_eq
        -- A is not on L, but X and A' are on L. So A, X, A' form a triangle.
        have h_tri : Triangle A X A' := by euclid_finish
        -- Since A' is the Foot of the perpendicular from A to L, and X is on L, angle A:A':X is a right angle.
        have h_ang_A' : ∠ A:A':X = ∟ := by
          have h := hA'.2.2 X
          have c : X.onLine L ∧ A' ≠ X := by euclid_finish
          specialize h c
          euclid_finish
        -- Similarly, since X is the Foot of the perpendicular from A to L, and A' is on L, angle A:X:A' is a right angle.
        have h_ang_X : ∠ A:X:A' = ∟ := by
          have h := h_foot_X.2.2 A'
          have c : A'.onLine L ∧ X ≠ A' := by euclid_finish
          specialize h c
          euclid_finish
        -- The sum of angles in Triangle A-X-A' is 180 degrees.
        have h_sum: ∠ A:X:A' + ∠ A:A':X + ∠ X:A:A' = ∟ + ∟ := by
          euclid_apply triangle_angles_sum A X A'
          euclid_finish
        -- This implies angle X:A:A' must be zero.
        have h_ang_A_is_zero : ∠ X:A:A' = 0 := by
          linarith
        -- A zero angle between segments from a common point implies the three points are collinear.
        have h_not_tri : ¬ Triangle A X A' := by euclid_finish
        contradiction
    -- Now we know that X and A' are the same point.
    -- We are given that M' passes through A (hM'.1) and X, so it must pass through A'.
    have h_A_on_M' : A.onLine M' := by euclid_finish
    have h_A'_on_M' : A'.onLine M' := by
      have h_X_on_M' : X.onLine M' := by euclid_finish
      have h_eq : X = A' := h_X_is_A'
      euclid_finish
    -- By hypothesis, x is on line M' (hx). Since A and A' are also on M', they are all collinear.
    have h_coll : Coll x A A' := by
      euclid_finish
    -- The line M was constructed as the line passing through A and A'.
    -- Any point collinear with A and A' must lie on M.
    euclid_finish

theorem foot_unique: ∀ (c h g: Point) (AB : Line), Foot c h AB ∧ Foot c g AB → h = g := by
  euclid_intros
  by_contra
  have h1: ∠c:h:g = ∟ := by
    euclid_finish
  have h2: ∠c:g:h = ∟ := by
    euclid_finish
  have h3: Triangle c g h := by
    euclid_finish
  euclid_apply triangle_angles_sum c g h
  euclid_apply line_from_points
  euclid_finish

theorem perpLine_imp_eq_sq_diff : ∀ (A B P Q : Point) (AB PQ : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine P Q PQ ∧ PerpLine AB PQ → |(A─P)| * |(A─P)| - |(A─Q)| * |(A─Q)| = |(B─P)| * |(B─P)| - |(B─Q)| * |(B─Q)| := by
    euclid_intros
    euclid_apply intersection_lines AB PQ as R
    by_cases h : R ≠ A ∧ R ≠ B ∧ R ≠ P ∧ R ≠ Q
    · euclid_apply PythagoreanTheorem_point R P A
      euclid_apply PythagoreanTheorem_point R Q A
      euclid_apply PythagoreanTheorem_point R P B
      euclid_apply PythagoreanTheorem_point R Q B
      euclid_finish
    · have h_1 : R = A ∨ R = B ∨ R = P ∨ R = Q := by
        euclid_finish
      rcases h_1 with h1|h2|h3|h4
      · by_cases R ≠ P ∧ R ≠ Q
        · euclid_apply PythagoreanTheorem_point R P B
          euclid_apply PythagoreanTheorem_point R Q B
          euclid_finish
        · by_cases R = P
          · euclid_apply PythagoreanTheorem_point R Q B
            euclid_finish
          · have tmp : R = Q := by euclid_finish
            euclid_apply PythagoreanTheorem_point R P B
            euclid_finish
      · by_cases R ≠ P ∧ R ≠ Q
        · euclid_apply PythagoreanTheorem_point R P A
          euclid_apply PythagoreanTheorem_point R Q A
          euclid_finish
        · by_cases R = P
          · euclid_apply PythagoreanTheorem_point R Q A
            euclid_finish
          · have tmp : R = Q := by euclid_finish
            euclid_apply PythagoreanTheorem_point R P A
            euclid_finish
      · by_cases R ≠ A ∧ R ≠ B
        · euclid_apply PythagoreanTheorem_point R Q A
          euclid_apply PythagoreanTheorem_point R Q B
          euclid_finish
        · by_cases R = A
          · euclid_apply PythagoreanTheorem_point R Q B
            euclid_finish
          · have tmp : R = B := by euclid_finish
            euclid_apply PythagoreanTheorem_point R Q A
            euclid_finish
      · by_cases R ≠ A ∧ R ≠ B
        · euclid_apply PythagoreanTheorem_point R P A
          euclid_apply PythagoreanTheorem_point R P B
          euclid_finish
        · by_cases R = A
          · euclid_apply PythagoreanTheorem_point R P B
            euclid_finish
          · have tmp : R = B := by euclid_finish
            euclid_apply PythagoreanTheorem_point R P A
            euclid_finish

theorem sq_diff_unique_onLine: ∀ (A B C D : Point) (AB : Line), distinctPointsOnLine A B AB ∧ C.onLine AB ∧ D.onLine AB ∧ |(C─A)| * |(C─A)| - |(C─B)| * |(C─B)| = |(D─A)| * |(D─A)| - |(D─B)| * |(D─B)| → C = D := by
    euclid_finish

theorem perpLine_if_eq_sq_diff_lemma : ∀ (A B P Q : Point) (AB PQ : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine P Q PQ ∧ |(A─P)| * |(A─P)| - |(A─Q)| * |(A─Q)| = |(B─P)| * |(B─P)| - |(B─Q)| * |(B─Q)| ∧ (A.onLine PQ ∨ B.onLine PQ ∨ P.onLine AB ∨ Q.onLine AB) → PerpLine AB PQ := by
  euclid_intros
  rcases right_3 with h1|h2|h3|h4
  · by_cases B.onLine PQ
    · euclid_apply sq_diff_unique_onLine P Q A B PQ
      euclid_finish
    · euclid_apply exists_foot B PQ as C
      euclid_apply line_from_points B C as BC
      euclid_apply perpLine_imp_eq_sq_diff B C P Q BC PQ
      euclid_apply sq_diff_unique_onLine P Q A C PQ
      euclid_finish
  · by_cases A.onLine PQ
    · euclid_apply sq_diff_unique_onLine P Q A B PQ
      euclid_finish
    · euclid_apply exists_foot A PQ as C
      euclid_apply line_from_points A C as AC
      euclid_apply perpLine_imp_eq_sq_diff A C P Q AC PQ
      euclid_apply sq_diff_unique_onLine P Q B C PQ
      euclid_finish
  · by_cases Q.onLine AB
    · euclid_apply sq_diff_unique_onLine A B P Q AB
      euclid_finish
    · euclid_apply exists_foot Q AB as R
      euclid_apply line_from_points Q R as QR
      euclid_apply perpLine_imp_eq_sq_diff Q R A B QR AB
      euclid_apply sq_diff_unique_onLine A B P R AB
      euclid_finish
  · by_cases P.onLine AB
    · euclid_apply sq_diff_unique_onLine A B P Q AB
      euclid_finish
    · euclid_apply exists_foot P AB as R
      euclid_apply line_from_points P R as PR
      euclid_apply perpLine_imp_eq_sq_diff P R A B PR AB
      euclid_apply sq_diff_unique_onLine A B Q R AB
      euclid_finish

theorem perpLine_if_eq_sq_diff : ∀ (A B P Q : Point) (AB PQ : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine P Q PQ ∧ |(A─P)| * |(A─P)| - |(A─Q)| * |(A─Q)| = |(B─P)| * |(B─P)| - |(B─Q)| * |(B─Q)| → PerpLine AB PQ := by
    euclid_intros
    by_cases h_0 : A.onLine PQ ∨ B.onLine PQ ∨ P.onLine AB ∨ Q.onLine AB
    · euclid_apply perpLine_if_eq_sq_diff_lemma A B P Q AB PQ
      euclid_finish
    · euclid_apply exists_foot P AB as R
      euclid_apply exists_foot Q AB as R'
      euclid_apply line_from_points P R as PR
      euclid_apply line_from_points Q R' as QR'
      euclid_apply perpLine_imp_eq_sq_diff P R A B PR AB
      euclid_apply perpLine_imp_eq_sq_diff Q R' A B QR' AB
      euclid_apply sq_diff_unique_onLine A B R R' AB
      by_cases A ≠ R
      · euclid_apply common_perpLine_imp_coll A R P Q
        euclid_finish
      · euclid_apply common_perpLine_imp_coll B R P Q
        euclid_finish

theorem PythagoreanTheorem_converse : ∀ (a b c: Point), (Triangle a b c) ∧ |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| → ∠ b:a:c = ∟ := by
    euclid_intros
    euclid_apply line_from_points a c as AC
    euclid_apply exists_foot b AC as d
    euclid_apply line_from_points b d as BD
    euclid_apply perpLine_imp_eq_sq_diff a c b d AC BD
    euclid_finish

end LeanGeo
