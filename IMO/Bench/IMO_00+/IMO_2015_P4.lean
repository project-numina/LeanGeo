import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Triangle $ABC$ has circumcircle $\Omega$ and circumcenter $O$. A circle $\Gamma$ with center $A$ intersects the segment $BC$ at points $D$ and $E$, such that $B$, $D$, $E$, and $C$ are all different and lie on line $BC$ in this order. Let $F$ and $G$ be the points of intersection of $\Gamma$ and $\Omega$, such that $A$, $F$, $B$, $C$, and $G$ lie on $\Omega$ in this order. Let $K$ be the second point of intersection of the circumcircle of triangle $BDF$ and the segment $AB$. Let $L$ be the second point of intersection of the circumcircle of triangle $CGE$ and the segment $CA$. Suppose that the lines $FK$ and $GL$ are different and intersect at the point $X$. Prove that $X$ lies on the line $AO$.
theorem IMO_2015_P4 :
  ∀ (A B C O D E F G K L X : Point) (BC AB CA : Line) (Ω Γ : Circle),
    formTriangle A B C AB BC CA ∧
    circumCentre O A B C ∧
    circumCircle Ω A B C ∧
    A.isCentre Γ ∧ D.onCircle Γ ∧ E.onCircle Γ ∧
    between B D E ∧ between D E C ∧
    circlesIntersectsAtTwoPoints Γ Ω F G ∧
    C.opposingSides F AB ∧ G.opposingSides B CA ∧
    cyclic B D F K ∧ between A K B ∧
    cyclic C G E L ∧ between C L A ∧
    ¬ coll F G K ∧
    coll F K X ∧ coll G L X
    → coll A O X := by
  sorry
