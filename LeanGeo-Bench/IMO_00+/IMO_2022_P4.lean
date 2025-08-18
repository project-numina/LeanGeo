import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABCDE$ be a convex pentagon such that $BC=DE$. Assume that there is a point $T$ inside $ABCDE$ with $TB=TD,TC=TE$ and $\angle ABT = \angle TEA$. Let line $AB$ intersect lines $CD$ and $CT$ at points $P$ and $Q$, respectively. Assume that the points $P,B,A,Q$ occur on their line in that order. Let line $AE$ intersect $CD$ and $DT$ at points $R$ and $S$, respectively. Assume that the points $R,E,A,S$ occur on their line in that order. Prove that the points $P,S,Q,R$ lie on a circle.
theorem IMO_2022_P4 :
  ∀ (A B C D E T P Q R S : Point)
    (AB BC CD DE EA CT DT : Line),
    formPentagon A B C D E AB BC CD DE EA ∧
    |(B─C)| = |(D─E)| ∧
    T.sameSide A BC ∧ T.sameSide B CD ∧ T.sameSide C DE ∧ T.sameSide D EA ∧ T.sameSide E AB ∧
    |(T─B)| = |(T─D)| ∧
    |(T─C)| = |(T─E)| ∧
    ∠ A:B:T = ∠ T:E:A ∧
    distinctPointsOnLine C T CT ∧
    distinctPointsOnLine D T DT ∧
    P.onLine AB ∧ P.onLine CD ∧
    Q.onLine AB ∧ Q.onLine CT ∧
    between P B A ∧ between B A Q ∧
    R.onLine EA ∧ R.onLine CD ∧
    S.onLine EA ∧ S.onLine DT ∧
    between R E A ∧ between E A S →
    Cyclic P S Q R := by
  sorry
