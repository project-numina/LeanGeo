import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Circle
import LeanGeo.Theorem.CirclePosition
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.PerpBisector
import LeanGeo.Theorem.Construction
namespace LeanGeo
theorem exists_circumCentre: ∀(A B C : Point), triangle A B C → ∃(O : Point), circumCentre O A B C := by
  euclid_intros
  euclid_apply threePoints_existCircle A B C as Ω
  euclid_apply exists_centre Ω as O
  use O
  euclid_finish

theorem triangle_perpBisector_concurrent: ∀(A B C: Point) (l1 l2 l3: Line), triangle A B C ∧ perpBisector A B l1 ∧ perpBisector B C l2 ∧ perpBisector A C l3 → concurrent l1 l2 l3 := by
  euclid_intros
  euclid_apply exists_circumCentre A B C as O
  use O
  euclid_apply perpBisector_property
  euclid_finish
