import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

namespace SystemE

opaque Angle : Point → Point → Point → ℝ
namespace Angle

opaque Right : ℝ

end Angle

notation "∟" => Angle.Right

notation:71 "∠" a ":" b ":" c:72 => Angle a b c

end SystemE
