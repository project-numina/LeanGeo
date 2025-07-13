import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--Two right-angled triangles, $\triangle ABC$ and $\triangle ADC$, share the same hypotenuse $AC$. The right angles are at vertices $B$ and $D$, respectively. Let $M$ be the midpoint of the hypotenuse $AC$. Assuming that the points $M$, $B$, and $D$ form a triangle, prove that this triangle is isosceles with $\angle MBD = \angle MDB$.-/

theorem right_triangles_share_hypotenuse_iso_angles:
  ∀ (A B C D M : Point),
    rightTriangle B A C ∧
    rightTriangle D A C ∧
    midpoint A M C ∧
    triangle M B D
    → ∠ M:B:D = ∠ M:D:B := by
    euclid_intros
    have h_MB_eq_MA : |(M─B)| = |(M─A)| := by
      euclid_apply rightTriangle_midLine_half B A C M
      euclid_finish
    have h_MD_eq_MA : |(M─D)| = |(M─A)| := by
      euclid_apply rightTriangle_midLine_half D A C M
      euclid_finish
    have h_MB_eq_MD : |(M─B)| = |(M─D)| := by
      euclid_finish
    have h_iso_MBD : isoTriangle M B D := by
      euclid_finish
    euclid_apply isoTriangle_eqAngle M B D
    euclid_finish
