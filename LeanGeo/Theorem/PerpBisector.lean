import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.BookTheorem
import LeanGeo.Theorem.Construction
import LeanGeo.Theorem.Basic
import LeanGeo.Theorem.Triangle

open LeanGeo Elements.Book1
namespace LeanGeo

theorem perpBisector_opposingSides:  ∀ (A B : Point) (L : Line),
perpBisector A B L → A.opposingSides B L := by
  euclid_intros
  euclid_apply exists_midpoint A B as M
  euclid_apply line_nonempty L as X1
  euclid_apply exists_distincts_points_on_line L X1 as X2
  euclid_apply line_from_points X1 A as X1A
  euclid_apply line_from_points X1 B as X1B
  euclid_apply line_from_points X2 A as X2A
  euclid_apply line_from_points X2 B as X2B
  have h1: ¬ A.sameSide B L := by
    by_contra
    euclid_apply proposition_7 X1 X2 A B L X1A X2A X1B X2B
    euclid_finish
  euclid_finish


theorem perpBisector_property : ∀ (A B : Point) (L : Line),
  perpBisector A B L →
  (∀ (X : Point), X.onLine L → |(X─A)| = |(X─B)|) ∧
  (∀ (X : Point), |(X─A)| = |(X─B)| → X.onLine L)
:= by
  euclid_intros
  euclid_apply perpBisector_opposingSides A B L
  constructor
  · euclid_finish
  · euclid_intros
    by_contra
    by_cases X.sameSide B L
    · euclid_apply line_from_points X A as XA
      euclid_assert XA.intersectsLine L
      obtain ⟨Y, hY⟩ := intersection_lines XA L  (by euclid_finish)
      euclid_assert triangle Y X B
      euclid_apply triangle_inequality X B Y
      have h1: |(X─Y)| + |(Y─A)| = |(X─A)| := by
        euclid_finish
      euclid_finish
    · euclid_assert X.sameSide A L
      euclid_apply line_from_points X B as XB
      euclid_assert XB.intersectsLine L
      obtain ⟨Y, hY⟩ := intersection_lines XB L  (by euclid_finish)
      euclid_assert triangle Y X A
      euclid_apply triangle_inequality X A Y
      have h1: |(X─Y)| + |(Y─B)| = |(X─B)| := by
        euclid_finish
      euclid_finish

theorem perpBisector_construction :
∀ (a b p q : Point) (L : Line),
(a ≠ b) ∧ (|(a─p)| = |(b─p)|) ∧ (|(a─q)| = |(b─q)|) ∧ distinctPointsOnLine p q L ∧ ¬ a.onLine L ∧ ¬ b.onLine L
→ perpBisector a b L := by
  euclid_intros
  simp
  constructor
  · euclid_finish
  · intro x hx
    by_cases (x ≠ p ∧ x ≠ q)
    · have h1: ∠x:p:a = ∠x:p:b := by
        have h2: ∠ q:p:a = ∠q:p:b := by
          euclid_apply congruent_SSS q p a q p b
          euclid_finish
        euclid_apply angle_between_transfer
        euclid_finish
      euclid_apply congruent_SAS x p a x p b
      euclid_finish
    · euclid_finish

theorem perpBisector_equiv : ∀ (A B : Point) (L: Line),
perpBisector A B L ↔ ∃ (P :Point) (AB : Line), P.onLine L ∧ midpoint A P B ∧ perpLine AB L ∧ distinctPointsOnLine A B AB := by
  euclid_intros
  constructor
  · intro h
    euclid_apply exists_midpoint A B as P
    euclid_apply line_from_points A B as AB
    euclid_apply perpBisector_property A B L
    use P
    use AB
    have h1: perpLine AB L := by
      use P
      constructor
      · euclid_finish
      · intro X Y h11 h12 h13 h14
        euclid_assert isoTriangle Y A B
        euclid_apply isoTriangle_threeLine_concidence_midpoint Y A B P
        euclid_finish
    euclid_finish
  · intro h
    simp
    constructor
    · euclid_finish
    · intro x hx
      rcases h with ⟨P, AB, hx⟩
      by_cases x = P
      · euclid_finish
      · euclid_assert rightTriangle P x A
        euclid_apply congruent_SAS x P A x P B
        euclid_finish



end LeanGeo
