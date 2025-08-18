import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Problem 1.41 (Russian Olympiad 1996). Points $E$ and $F$ are on side $\overline{B C}$ of convex quadrilateral $A B C D$ (with $E$ closer than $F$ to $B$ ). It is known that $\angle B A E=\angle C D F$ and $\angle E A F=\angle F D E$. Prove that $\angle F A C=\angle E D B$.
theorem Russian_Olympiad_1_41 :
  ∀ (A B C D E F : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    between B E F ∧
    between B F C ∧
    ∠ B:A:E = ∠ C:D:F ∧
    ∠ E:A:F = ∠ F:D:E →
    ∠ F:A:C = ∠ E:D:B := by
  sorry