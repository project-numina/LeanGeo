import SystemE.Theory.Sorts.Primitives
import Mathlib.Data.Real.Basic

namespace SystemE
opaque length : Point → Point → ℝ

open Lean PrettyPrinter

syntax "(" term "─" term ")": term

macro_rules
| `(|($t:term ─ $s:term)|) => `(length $t $s)

@[app_unexpander length]
def unexpand_endpoints : Unexpander
| `($_ $t $s) => `(|($t ─ $s)|)
| _ => throw ()

end SystemE
