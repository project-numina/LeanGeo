import SystemE.Theory.Sorts.Segments

namespace LeanGeo

opaque area' : Point → Point → Point → ℝ

inductive triangle
| ofPoints (a b c : Point)

@[simp]
abbrev triangle.area : triangle → ℝ :=
  fun x =>
    match x with
    | ofPoints a b c => area' a b c


notation:max "△" a ":" b ":" c:66 => triangle.ofPoints a b c

instance : Coe triangle ℝ :=
  ⟨triangle.area⟩

-- example (a b c : Point) : triangle.area (△ a:b:c) = 0 := by
--   dsimp

end LeanGeo
