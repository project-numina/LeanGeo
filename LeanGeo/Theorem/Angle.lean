import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.BookTheorem

open LeanGeo
namespace LeanGeo

theorem angle_coincide_zero : ∀ (a o : Point), (a ≠ o) → ∠a:o:a = 0:= by
  euclid_intros

  euclid_apply line_from_points
  euclid_finish

theorem supplementaryAngle_line : ∀ (d a b c: Point), (between a b c) ∧ (¬ coll a b d) → ∠d:b:a + ∠d:b:c = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b d as BD
  euclid_apply Book_between_angleSum d b c a BD AB
  euclid_finish

theorem between_zeroAngle : ∀ (A B C : Point), between A B C → ∠B:A:C = 0 := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_finish

theorem sameSide_eqAngle_coll : ∀(A B C D: Point) (AB : Line), distinctPointsOnLine A B AB ∧ (∠A:B:C = ∠A:B:D) ∧ D.sameSide C AB → coll B C D := by
  euclid_intros
  euclid_apply line_from_points B C as BC
  have h1: ¬ (D.sameSide A BC):= by
    --by_contra
    --euclid_assert ∠D:B:C + ∠A:B:C = ∠D:B:A
    euclid_finish
  have h2:  ¬ (D.opposingSides A BC) := by
    by_contra
    euclid_apply line_from_points
    euclid_assert ∠D:B:C + ∠A:B:C = ∠D:B:A
    euclid_finish
  euclid_finish

theorem between_straightAngle : ∀ (A B C : Point), between A B C → ∠A:B:C = ∟  + ∟ := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_finish

theorem coll_exist_line : ∀ (A B C : Point), coll A B C → ∃(l:Line),
A.onLine l ∧ B.onLine l ∧ C.onLine l := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply exists_distincts_points_on_line
  euclid_finish

theorem point_not_onLine : ∀(A B C : Point) (l :Line), ¬ coll A B C ∧ distinctPointsOnLine B C l → ¬ A.onLine l := by
  euclid_intros
  euclid_finish

--theorem angle_positive_neq : ∀ (a o b : Point), (∠a:o:b>0) → (a ≠ b) ∧ (a ≠ o) ∧ (b ≠ o) := by
--  sorry
theorem angle_between_transfer : ∀ (a b c d : Point),between a b c ∧ ¬ coll a b d → ∠d:c:b = ∠d:c:a ∧ ∠d:b:c + ∠d:b:a = ∟ + ∟ ∧ ∠d:a:b = ∠d:a:c:= by
  euclid_intros
  constructor
  · euclid_apply line_from_points
    euclid_finish
  · constructor
    · euclid_apply supplementaryAngle_line
      euclid_finish
    · euclid_apply line_from_points
      euclid_finish

theorem coll_equal_or_complement: ∀ (A B C D: Point), coll A B C  ∧ (B ≠ C) ∧ (B ≠ A) ∧ (C ≠ A) ∧ ¬ ( coll A B D)→
  ∠ D:B:C = ∠ D:B:A ∨ ∠ D:B:C + ∠D:B:A = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points B C as L
  by_cases between A B C
  · euclid_apply angle_between_transfer A B C D
    euclid_finish
  · by_cases between A C B
    · euclid_apply angle_between_transfer A C B D
      euclid_finish
    · euclid_apply angle_between_transfer C A B D
      euclid_finish

theorem between_angleSum : ∀(a b c d: Point), between b c d ∧ (¬ coll a b c) → ∠d:a:c + ∠c:a:b = ∠d:a:b:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem angle_bisector_between: ∀ (a b c d: Point), (triangle a b c) ∧ (coll b d c) ∧ (∠d:a:c = ∠d:a:b) → between b d c := by
  euclid_intros
  euclid_apply line_from_points
  euclid_assert d ≠ a
  have :d ≠ b := by
    by_contra
    euclid_apply angle_coincide_zero d a
    euclid_assert ∠b:a:c = 0
    euclid_finish
  have : d ≠ c := by
    by_contra
    euclid_apply angle_coincide_zero d a
    euclid_finish
  have : ¬ (between d c b) := by
    by_contra
    euclid_apply between_angleSum a b c d
    euclid_finish
  have : ¬ (between c b d) := by
    by_contra
    euclid_apply between_angleSum a c b d
    euclid_finish
  euclid_finish

theorem opposite_angles_same : ∀ (A B C D E: Point), between A C E ∧ between B C D → ∠A:C:B = ∠ D:C:E := by
  euclid_intros
  by_cases coll A B C
  · euclid_apply line_from_points
    euclid_finish
  · euclid_apply line_from_points
    euclid_apply angle_between_transfer
    euclid_finish
end LeanGeo
