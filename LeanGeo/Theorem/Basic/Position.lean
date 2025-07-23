import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle

namespace LeanGeo
open Elements.Book1

theorem angleBisector_opposingSides : ∀ (A B C I : Point) (AI : Line), (distinctPointsOnLine A I AI) ∧ Triangle A B C ∧ ∠ I:A:B = ∠ I:A:C →  B.opposingSides C AI := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_finish

theorem acuteAngle_foot_on_ray : ∀(A B C D: Point) (BC: Line), distinctPointsOnLine B C BC ∧ Foot A D BC ∧ ∠A:B:C < ∟ → LiesOnRay B C D := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A D as AD
  euclid_apply proposition_17 A B D AB BC AD
  by_cases D = B
  · euclid_finish
  · euclid_apply coll_supp_angles A D B C
    euclid_finish

theorem obutseAngle_foot_on_ray : ∀(A B C D: Point) (BC: Line), distinctPointsOnLine B C BC ∧ Foot A D BC ∧ ∠A:B:C > ∟ → between D B C := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A D as AD
  euclid_apply proposition_17 A B D AB BC AD
  euclid_finish

end LeanGeo
