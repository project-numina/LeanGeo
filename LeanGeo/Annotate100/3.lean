import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--## G1 MNE

Around the triangle $A B C$ the circle is circumscribed, and at the vertex $C$ tangent $t$ to this circle is drawn. The line $p$ which is parallel to this tangent intersects the lines $B C$ and $A C$ at the points $D$ and $E$, respectively. Prove that the points $A, B, D, E$ belong to the same circle.

-/
theorem Numina_Geometry_19 :
  ∀ (A B C D E : Point) (AB BC CA p t : Line) (O : Circle),
    formTriangle A B C AB BC CA ∧
    circumCircle O A B C ∧
    tangentAtPoint t O C ∧
    p ≠ t ∧
    (¬ p.intersectsLine t) ∧
    D.onLine p ∧
    D.onLine BC ∧
    E.onLine p ∧
    E.onLine CA →
    cyclic A B D E := by
    sorry
