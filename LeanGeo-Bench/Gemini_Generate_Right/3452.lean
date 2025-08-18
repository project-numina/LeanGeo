import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem cyclic_collinearity_from_exterior_angle :
  ∀ (A B C D E F : Point) (AB BC CD DA : Line) (Ω : Circle),
    CyclicQuadrilateral A B C D AB BC CD DA Ω ∧
    between A B E ∧
    A.sameSide F CD ∧
    ∠ E:B:C = ∠ F:D:C
  → Coll A D F := by
  euclid_intros
  -- Step 1: Establish that the exterior angle of the Cyclic quadrilateral at vertex B
  -- is equal to the interior opposite angle at vertex D.
  sorry
