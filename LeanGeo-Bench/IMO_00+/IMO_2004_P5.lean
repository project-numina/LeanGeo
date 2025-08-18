import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--In a convex quadrilateral $ABCD$, the diagonal $BD$ bisects neither the angle $ABC$ nor the angle $CDA$. The point $P$ lies inside $ABCD$ and satisfies\[\angle PBC=\angle DBA\quad	ext{and}\quad \angle PDC=\angle BDA.\]Prove that $ABCD$ is a Cyclic quadrilateral if and only if $AP=CP$.
theorem IMO_2004_P5 :
  ∀ (A B C D P : Point) (AB BC CD DA BD : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ¬ (∠ A:B:D = ∠ D:B:C) ∧
    ¬ (∠ C:D:B = ∠ B:D:A) ∧
    InsideQuadrilateral P A B C D AB BC CD DA ∧
    ∠ P:B:C = ∠ D:B:A ∧
    ∠ P:D:C = ∠ B:D:A →
    (Cyclic A B C D ↔ |(A─P)| = |(C─P)|) := by
  sorry
