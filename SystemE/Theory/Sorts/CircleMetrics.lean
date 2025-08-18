import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

namespace LeanGeo
namespace CircleMetrics

opaque radius : Circle → ℝ

opaque circlePower : Point → Circle → ℝ

notation:73 "Pow(" p "," O ")"=> circlePower p O

notation:74 "rad" O => radius O

end CircleMetrics
end LeanGeo
