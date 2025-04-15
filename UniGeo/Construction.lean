import SystemE
@[simp]
abbrev formIsotriangle (a b c : Point) (AB BC CA : Line) : Prop :=
  formTriangle a b c AB BC CA ∧ |(a─b)| = |(a─c)|

@[simp]
axiom isotriangle_eqangle (a b c : Point) (AB BC CA : Line) :
    formIsotriangle a b c AB BC CA → ∠ a:b:c = ∠ a:c:b

@[simp]
axiom eqangle_isotriangle (a b c : Point) (AB BC CA : Line) :
    formTriangle a b c AB BC CA → ∠ a:b:c = ∠ a:c:b → |(a─b)| = |(a─c)|


inductive Quadrilateral
| ofPoints (a b c d : Point)


namespace Quadrilateral
notation:max "Quadri" a ":" b ":" c ":" d => ofPoints a b c d

@[simp]
abbrev cyclic (Q: Quadrilateral): Prop :=
  match Q with
  | (Quadrilateral.ofPoints A B C D) =>
  (∠ A:B:D = ∠ A:C:D) ∨
  (∠ D:A:C = ∠ D:B:C) ∨
  (∠ A:D:B = ∠ A:C:B) ∨
  (∠ B:D:C = ∠ B:A:C) ∨
  (∃ O: Circle, A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O) ∨
  (∠ A:D:C + ∠A:B:C = ∟ + ∟) ∧
  (∠ D:A:B + ∠D:C:B = ∟ + ∟)

axiom cyclic_if (Q: Quadrilateral): cyclic Q →
  match Q with
  | (Quadrilateral.ofPoints A B C D) =>
  (∠ A:B:D = ∠ A:C:D) ∧
  (∠ D:A:C = ∠ D:B:C) ∧
  (∠ A:D:B = ∠ A:C:B) ∧
  (∠ B:D:C = ∠ B:A:C) ∧
  (∃ O: Circle, A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O) ∧
  (∠ A:D:C + ∠A:B:C = ∟ + ∟) ∧
  (∠ D:A:B + ∠D:A:C = ∟ + ∟)


end Quadrilateral
