import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Lemma 1.42. Let $ABC$ be an acute Triangle inscribed in circle $\Omega$. Let $X$ be the MidPoint of the arc $\widehat{BC}$ not containing $A$ and define $Y, Z$ similarly. Show that the orthocenter of XYZ is the incenter I of ABC.
theorem Lemma1_42 :
  ∀ (A B C I X Y Z D E F : Point) (AB BC CA XY YZ ZX : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    Circumcircle Ω A B C ∧
    X.onCircle Ω ∧ |(X─B)| = |(X─C)| ∧ X.opposingSides A BC ∧
    Y.onCircle Ω ∧ |(Y─C)| = |(Y─A)| ∧ Y.opposingSides B CA ∧
    Z.onCircle Ω ∧ |(Z─A)| = |(Z─B)| ∧ Z.opposingSides C AB ∧
    Incentre I A B C ∧
    distinctPointsOnLine Y Z YZ ∧
    Foot X D YZ
    → Coll X I D:= by
  sorry
