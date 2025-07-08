import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
/--4. A square $O M K N$ is inscribed in a circle such that vertex $O$ coincides with the center of the circle, and vertex $K$ lies on the circle. Chord $A B$ of the circle passes through vertex $M$, and chord $\mathrm{CD}$ passes through vertex $\mathrm{N}$. Prove that $A M \cdot M B=C N \cdot N D$.-/
theorem Numina_Geometry_925 :
  ∀ (O M K N A B C D : Point) (Ω : Circle)
    (OM MK KN NO AB CD : Line),
    square O M K N OM MK KN NO ∧
    O.isCentre Ω ∧
    K.onCircle Ω ∧
    threePointsOnLine A M B AB ∧
    threePointsOnLine C N D CD ∧
    A.onCircle Ω ∧
    B.onCircle Ω ∧
    C.onCircle Ω ∧
    D.onCircle Ω →
    |(A─M)| * |(M─B)| = |(C─N)| * |(N─D)| := by
    euclid_intros
    have h1: M.insideCircle Ω := by
      have h2: |(M─O)| < |(K─O)| := by
        euclid_apply pythagorean_point M O K
        euclid_finish
      euclid_finish
    have h3: N.insideCircle Ω := by
      have h4: |(N─O)| < |(K─O)| := by
        euclid_apply pythagorean_point N O K
        euclid_finish
      euclid_finish
    euclid_apply inside_power M O A B Ω
    euclid_apply inside_power N O C D Ω
    have h3: |(M─O)| = |(N─O)| := by
      euclid_finish
    euclid_finish
--11s
