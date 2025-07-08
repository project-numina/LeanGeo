import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--2. In a convex quadrilateral $A B C D$, point $K$ is the midpoint of $A B$, point $L$ is the midpoint of $B C$, point $M$ is the midpoint of $C D$, and point $N$ is the midpoint of $D A$. For some point $S$ lying inside the quadrilateral $A B C D$, it turns out that $K S=L S$ and $N S=M S$. Prove that $\angle K S N=\angle M S L$.-/
theorem Numina_Geometry_932 :
  ∀ (A B C D K L M N S : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    midpoint A K B ∧
    midpoint B L C ∧
    midpoint C M D ∧
    midpoint D N A ∧
    triangle K L S ∧ triangle N M S ∧
    |(K─S)| = |(L─S)| ∧
    |(N─S)| = |(M─S)|
    → ∠ K:S:N = ∠ M:S:L := by
    euclid_intros
    have h1: |(K─N)| = |(M─L)| := by
      have h2: |(K─N)| * 2 = |(B─D)|:= by
        euclid_apply triangle_median_line_half A B D K N
        euclid_finish
      have h3: |(L─M)| * 2 = |(B─D)|:= by
        euclid_apply triangle_median_line_half C B D L M
        euclid_finish
      euclid_finish
    euclid_apply (△ K:N:S).congruent_property ((△ L:M:S))
    euclid_finish
