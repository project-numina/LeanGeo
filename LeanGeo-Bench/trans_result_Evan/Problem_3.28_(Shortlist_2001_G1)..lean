import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $A_1$ be the center of the Square inscribed in acute Triangle $A B C$ with two vertices of the Square on side $B C$. Thus one of the two remaining vertices of the Square is on side $A B$ and the other is on $A C$. Points $B_1$ and $C_1$ are defined in a similar way for inscribed squares with two vertices on sides $A C$ and $A B$, respectively. Prove that lines $A A_1, B B_1, C C_1$ are concurrent.
theorem Problem_3_28_Shortlist_2001_G1 :
  ∀ (A B C A1 B1 C1 P Q R S U V W X M N L K : Point)
    (AB BC CA lPQ lQR lRS lSP lUV lVW lWX lXU lMN lNL lLK lKM lAA1 lBB1 lCC1 : Line),
    formAcuteTriangle A B C AB BC CA ∧
    Square P Q R S lPQ lQR lRS lSP ∧ P.onLine BC ∧ Q.onLine BC ∧ R.onLine CA ∧ S.onLine AB ∧
    MidPoint P A1 R ∧ MidPoint Q A1 S ∧
    Square U V W X lUV lVW lWX lXU ∧ U.onLine CA ∧ V.onLine CA ∧ W.onLine AB ∧ X.onLine BC ∧
    MidPoint U B1 W ∧ MidPoint V B1 X ∧
    Square M N L K lMN lNL lLK lKM ∧ M.onLine AB ∧ N.onLine AB ∧ L.onLine BC ∧ K.onLine CA ∧
    MidPoint M C1 L ∧ MidPoint N C1 K ∧
    distinctPointsOnLine A A1 lAA1 ∧ distinctPointsOnLine B B1 lBB1 ∧ distinctPointsOnLine C C1 lCC1 →
    Concurrent lAA1 lBB1 lCC1 := by
  sorry
