import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--Two right-angled triangles, $\triangle ABC$ and $\triangle ADC$, share the same hypotenuse $AC$. The right angles are at vertices $B$ and $D$, respectively. Let $M$ be the MidPoint of the hypotenuse $AC$. Assuming that the points $M$, $B$, and $D$ form a triangle, prove that this Triangle is isosceles with $\angle MBD = \angle MDB$.-/

theorem right_triangles_share_hypotenuse_iso_angles:
  ∀ (A B C D M : Point),
    RightTriangle B A C ∧
    RightTriangle D A C ∧
    MidPoint A M C ∧
    Triangle M B D
    → ∠ M:B:D = ∠ M:D:B := by
    euclid_intros
    have h_MB_eq_MA : |(M─B)| = |(M─A)| := by
      euclid_apply rightTriangle_midLine_eq_half_hypotenuse B A C M
      euclid_finish
    have h_MD_eq_MA : |(M─D)| = |(M─A)| := by
      euclid_apply rightTriangle_midLine_eq_half_hypotenuse D A C M
      euclid_finish
    have h_MB_eq_MD : |(M─B)| = |(M─D)| := by
      euclid_finish
    have h_iso_MBD : IsoTriangle M B D := by
      euclid_finish
    euclid_apply isoTriangle_imp_eq_angles M B D
    euclid_finish
