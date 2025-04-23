import SystemE
import Book.Prop28
import UniGeo.Relations

namespace UniGeo.Quadrilateral

theorem theorem_20 : ∀ (Q R S T U : Point) (QR ST RS QT QS RT : Line),
  formQuadrilateral Q R T S QR ST QT RS ∧
  distinctPointsOnLine Q S QS ∧
  distinctPointsOnLine R T RT ∧
  twoLinesIntersectAtPoint QS RT U ∧
  ∠ Q:T:S = ∠ Q:R:S ∧
  ∠ R:S:T = ∠ R:Q:T →
  ¬ QT.intersectsLine RS :=
by
  sorry

end UniGeo.Quadrilateral
