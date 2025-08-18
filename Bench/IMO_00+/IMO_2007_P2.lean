import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Consider five points $A$, $B$, $C$, $D$ and $E$ such that $ABCD$ is a parallelogram and $BCED$ is a cyclic quadrilateral. Let $\ell$ be a line passing through $A$. Suppose that $\ell$ intersects the interior of the segment $DC$ at $F$ and intersects line $BC$ at $G$. Suppose also that $EF = EG = EC$. Prove that $\ell$ is the bisector of angle $DAB$.
theorem IMO_2007_P2 :
  ∀ (A B C D E F G : Point) (AB BC CD DA l : Line),
    parallelogram A B C D AB BC CD DA ∧
    cyclic B C E D ∧
    A.onLine l ∧
    between D F C ∧ F.onLine l ∧
    G.onLine BC ∧ G.onLine l ∧
    |(E─F)| = |(E─G)| ∧ |(E─G)| = |(E─C)| →
    ∠ D:A:G = ∠ G:A:B := by
  sorry
