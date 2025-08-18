import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import Book
namespace LeanGeo

open Elements.Book1

theorem coincident_angle_eq_zero : ∀ (A B : Point), (A ≠ B) → ∠A:B:A = 0:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem coll_def : ∀ (A B C : Point), Coll A B C → ∃(l:Line),
A.onLine l ∧ B.onLine l ∧ C.onLine l := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply exists_distincts_points_on_line
  euclid_finish

theorem not_coll_not_onLine : ∀(A B C : Point) (l :Line), ¬ Coll A B C ∧ distinctPointsOnLine B C l → ¬ A.onLine l := by
  euclid_intros
  euclid_finish

theorem coll_zeroAngle : ∀ (A B C : Point), between A B C → ∠B:A:C = 0 := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_finish

theorem coll_straightAngle : ∀ (A B C : Point), between A B C → ∠A:B:C = ∟  + ∟ := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_finish

theorem coll_supp_angles : ∀ (D A B C: Point), (between A B C) ∧ (¬ Coll A B D) → ∠D:B:A + ∠D:B:C = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B D as BD
  euclid_apply proposition_13 D B C A BD AB
  euclid_finish

theorem coll_angles_eq : ∀ (A B C D : Point), between A B C ∧ ¬ Coll A B D → ∠D:C:B = ∠D:C:A ∧ ∠D:B:C + ∠D:B:A = ∟ + ∟ ∧ ∠D:A:B = ∠D:A:C:= by
  euclid_intros
  constructor
  · euclid_apply line_from_points
    euclid_finish
  · constructor
    · euclid_apply coll_supp_angles
      euclid_finish
    · euclid_apply line_from_points
      euclid_finish

theorem nondegenerate_angle_if : ∀ (A B C : Point), ¬ Coll A B C → ∠A:B:C > 0 ∧ ∠A:B:C < ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply extend_point AB A B as D
  euclid_apply coll_supp_angles C A B D
  euclid_finish

theorem nondegenerate_angle_onlyif : ∀ (A B C : Point), ∠A:B:C > 0 ∧ ∠A:B:C < ∟ + ∟ ∧ A ≠ B ∧ B ≠ C → ¬ Coll A B C := by
  euclid_intros
  euclid_apply coincident_angle_eq_zero
  euclid_apply coll_straightAngle
  euclid_apply coll_zeroAngle
  euclid_finish

theorem coll_if_eq_angles : ∀(A B C D: Point) (AB : Line), distinctPointsOnLine A B AB ∧ (∠A:B:C = ∠A:B:D) ∧ D.sameSide C AB → Coll B C D := by
  euclid_intros
  euclid_apply line_from_points B C as BC
  have h1: ¬ (D.sameSide A BC):= by
    euclid_finish
  have h2:  ¬ (D.opposingSides A BC) := by
    by_contra
    euclid_apply line_from_points
    euclid_assert ∠D:B:C + ∠A:B:C = ∠D:B:A
    euclid_finish
  euclid_finish

theorem coll_if_supp_angles : ∀(A B C D: Point) (AB : Line), distinctPointsOnLine A B AB ∧ (∠A:B:C + ∠A:B:D = ∟ + ∟ ) ∧ D.opposingSides C AB → between C B D := by
  euclid_intros
  euclid_apply line_from_points B D as BD
  euclid_apply extend_point BD D B as E
  euclid_apply coll_angles_eq
  euclid_assert E.sameSide C AB
  euclid_apply coll_if_eq_angles A B C E
  euclid_finish

theorem coll_eq_or_supp_angles: ∀ (A B C D: Point), Coll A B C  ∧ (B ≠ C) ∧ (B ≠ A) ∧ (C ≠ A) ∧ ¬ ( Coll A B D)→
  ∠ D:B:C = ∠ D:B:A ∨ ∠ D:B:C + ∠D:B:A = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points B C as L
  by_cases between A B C
  · euclid_apply coll_angles_eq A B C D
    euclid_finish
  · by_cases between A C B
    · euclid_apply coll_angles_eq A C B D
      euclid_finish
    · euclid_apply coll_angles_eq C A B D
      euclid_finish

theorem between_imp_angles_sum : ∀(A B C D: Point), between B C D ∧ (¬ Coll A B C) → ∠D:A:C + ∠C:A:B = ∠D:A:B := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem between_if_angles_sum: ∀ (A B C D: Point), (Triangle A B C) ∧ (Coll B D C) ∧ (∠D:A:C = ∠D:A:B) → between B D C := by
  euclid_intros
  euclid_apply line_from_points
  euclid_assert D ≠ A
  have : D ≠ B := by
    by_contra
    euclid_apply coincident_angle_eq_zero D A
    euclid_assert ∠B:A:C = 0
    euclid_finish
  have : D ≠ C := by
    by_contra
    euclid_apply coincident_angle_eq_zero D A
    euclid_finish
  have : ¬ (between D C B) := by
    by_contra
    euclid_apply between_imp_angles_sum A B C D
    euclid_finish
  have : ¬ (between C B D) := by
    by_contra
    euclid_apply between_imp_angles_sum A C B D
    euclid_finish
  euclid_finish

theorem eq_opposite_angles : ∀ (A B C D E: Point), between A C E ∧ between B C D → ∠A:C:B = ∠ D:C:E := by
  euclid_intros
  by_cases Coll A B C
  · euclid_apply line_from_points
    euclid_finish
  · euclid_apply line_from_points
    euclid_apply coll_angles_eq
    euclid_finish

theorem triangle_angles_sum : ∀(A B C : Point) , Triangle A B C → ∠A:B:C +∠B:C:A + ∠C:A:B = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points C A as CA
  euclid_apply extend_point BC B C as D
  euclid_apply proposition_32 A B C D AB BC CA
  euclid_finish

theorem completeQuadrilateral_angles_sum : ∀ (A B C D E F: Point) (ABC CDF BDE AEF : Line), CompleteQuadrilateral A B C D E F ABC CDF BDE AEF → ∠E:A:C + ∠A:E:D + ∠A:C:D = ∠E:D:C := by
  euclid_intros
  euclid_apply triangle_angles_sum A B E
  euclid_apply triangle_angles_sum B D C
  euclid_apply coll_supp_angles C B D E
  euclid_apply coll_supp_angles E A B C
  euclid_finish

theorem acuteAngle_foot_eq_angles : ∀ (A B C D : Point) (BC: Line), distinctPointsOnLine B C BC ∧ ¬ (A.onLine BC) ∧ Foot A D BC ∧ ∠A:B:C < ∟ → ∠A:B:C = ∠A:B:D := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply triangle_angles_sum
  euclid_finish

end LeanGeo
