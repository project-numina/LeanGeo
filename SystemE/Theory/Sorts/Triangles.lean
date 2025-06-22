import SystemE.Theory.Sorts.Segments

namespace SystemE

opaque area' : Point → Point → Point → ℝ

inductive Triangle
| ofPoints (a b c : Point)

@[simp]
abbrev Triangle.area : Triangle → ℝ :=
  fun x =>
    match x with
    | ofPoints a b c => area' a b c


notation:max "△" a ":" b ":" c:66 => Triangle.ofPoints a b c

instance : Coe Triangle ℝ :=
  ⟨Triangle.area⟩

-- example (a b c : Point) : Triangle.area (△ a:b:c) = 0 := by
--   dsimp

end SystemE
