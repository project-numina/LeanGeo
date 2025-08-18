import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Suppose $\triangle A B C$ is a triangle with incenter $I$. Show that the circumcenters of $\triangle I A B, \triangle I B C$, and $\triangle I C A$ lie on a circle whose center is the circumcenter of $\triangle A B C$.
theorem Problem_4_42_USAMO_1988_4 :
  ∀ (A B C I O O1 O2 O3 : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    inCentre I A B C ∧
    circumCentre O A B C ∧
    circumCentre O1 I A B ∧
    circumCentre O2 I B C ∧
    circumCentre O3 I C A →
    |(O─O1)| = |(O─O2)| ∧ |(O─O2)| = |(O─O3)| := by
  sorry