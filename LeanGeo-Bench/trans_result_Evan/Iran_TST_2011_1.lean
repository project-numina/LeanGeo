import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--In acute Triangle $A B C, \angle B$ is greater than $\angle C$. Let $M$ be the MidPoint of $\overline{B C}$ and let $E$ and $F$ be the feet of the altitudes from $B$ and $C$, respectively. Let $K$ and $L$ be the midpoints of $\overline{M E}$ and $\overline{M F}$, respectively, and let $T$ be on line $K L$ such that $\overline{T A} \| \overline{B C}$. Prove that $T A=T M$.
theorem Iran_TST_2011_1 :
  ∀ (A B C M E F K L T : Point) (AB BC CA KL AT : Line),
    formAcuteTriangle A B C AB BC CA ∧
    ∠ A:B:C > ∠ B:C:A ∧
    MidPoint B M C ∧
    Foot B E CA ∧
    Foot C F AB ∧
    MidPoint M K E ∧
    MidPoint M L F ∧
    distinctPointsOnLine K L KL ∧
    T.onLine KL ∧
    distinctPointsOnLine A T AT ∧
    ¬(AT.intersectsLine BC) →
    |(T─A)| = |(T─M)| := by
  sorry
