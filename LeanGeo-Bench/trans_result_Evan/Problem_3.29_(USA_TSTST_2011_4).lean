import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Acute Triangle $A B C$ is inscribed in circle $\omega$. Let $H$ and $O$ denote its orthocenter and circumcenter, respectively. Let $M$ and $N$ be the midpoints of sides $A B$ and $A C$, respectively. Rays $M H$ and $N H$ meet $\omega$ at $P$ and $Q$, respectively. Lines $M N$ and $P Q$ meet at $R$. Prove that $\overline{O A} \perp \overline{R A}$.
theorem Problem_3_29_USA_TSTST_2011_4 :
  ∀ (A B C D E F H O M N P Q R D E F : Point) (ω : Circle) (AB BC CA MN PQ : Line),
    formAcuteTriangle A B C AB BC CA ∧
    Orthocentre H A B C D E F AB BC CA ∧
    Circumcentre O A B C ∧
    Circumcircle ω A B C ∧
    MidPoint A M B ∧
    MidPoint A N C ∧
    between M H P ∧
    P.onCircle ω ∧
    between N H Q ∧
    Q.onCircle ω ∧
    distinctPointsOnLine M N MN ∧
    R.onLine MN ∧
    R.onLine PQ →
    ∠O:A:R = ∟ := by
  sorry
