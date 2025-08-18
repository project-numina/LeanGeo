import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--Problem 7. Given a Triangle $ABC$. Let $BL$ be the bisector of Triangle $ABC$ ($L$ on segment $AC$), and $X$ be a point on segment $AB$ such that $XL \parallel BC$. The circumcircle of Triangle $AXC$ intersects segment $BC$ at points $C$ and $Y$. Prove that $AX = BY$.-/
theorem Numina_Geometry_800 : ∀ (A B C L X Y : Point) (XL BC: Line) (Ω : Circle),
  Triangle A B C ∧
  between A L C ∧
  between A X B ∧
  (∠ A:L:B = ∠ B:L:C) ∧
  distinctPointsOnLine X L XL ∧
  distinctPointsOnLine B C BC ∧
  (¬ XL.intersectsLine BC) ∧
  Circumcircle Ω A X C ∧
  Y.onCircle Ω ∧
  between B Y C
  → |(A─X)| = |(B─Y)| := by
  sorry
