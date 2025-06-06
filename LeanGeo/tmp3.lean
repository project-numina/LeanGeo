import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem inscribed_trapezoid_isosceles_0: ∀ (A B C D: Point) (P : Circle) (AB BC CD DA : Line),
(cyclicQuadrilateral A B C D AB BC CD DA P) ∧ (¬ AB.intersectsLine CD)
→ |(B─C)| = |(A─D)| := by
  euclid_intros
  euclid_apply cyclic_property
  euclid_finish
