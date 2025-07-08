import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $\Gamma$ be a circle with centre $I$, and $A B C D$ a convex quadrilateral such that each of the segments $A B, B C, C D$ and $D A$ is tangent to $\Gamma$. Let $\Omega$ be the circumcircle of the triangle $A I C$. The extension of $B A$ beyond $A$ meets $\Omega$ at $X$, and the extension of $B C$ beyond $C$ meets $\Omega$ at $Z$. The extensions of $A D$ and $C D$ beyond $D$ meet $\Omega$ at $Y$ and $T$, respectively. Prove that\[A D+D T+T X+X A=C D+D Y+Y Z+Z C.\]
theorem IMO_2021_P4 :
  ∀ (A B C D I X Y Z T : Point) (Γ Ω : Circle) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    I.isCentre Γ ∧
    tangentLine AB Γ ∧ tangentLine BC Γ ∧ tangentLine CD Γ ∧ tangentLine DA Γ ∧
    circumCircle Ω A I C ∧
    X.onCircle Ω ∧ between B A X ∧
    Z.onCircle Ω ∧ between B C Z ∧
    Y.onCircle Ω ∧ between A D Y ∧
    T.onCircle Ω ∧ between C D T →
    |(A─D)| + |(D─T)| + |(T─X)| + |(X─A)| =
    |(C─D)| + |(D─Y)| + |(Y─Z)| + |(Z─C)| := by
  sorry