import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

/--
An angle ∠ABC is defined by three points.
-/
inductive DAngle
| ofPoints (A B C : Point)

namespace DAngle
opaque degree : DAngle → ℝ
instance : Coe DAngle ℝ := ⟨degree⟩

end DAngle

notation "∟" => DAngle.Right

notation:71 "∠" a "," b "," c:72 => DAngle.degree (DAngle.ofPoints a b c)

open Lean PrettyPrinter

@[app_unexpander DAngle.degree]
def unexpand_degree : Unexpander
| `($_ (`DAngle.ofPoints $a:ident $b:ident $c:ident)) => `(∠ $a:ident , $b:ident , $c:ident)
| _ => throw ()
