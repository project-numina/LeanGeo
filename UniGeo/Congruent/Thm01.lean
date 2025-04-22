import SystemE
import Book.Prop29
import SystemE.Theory.Relations
import UniGeo.Abbre
namespace UniGeo.Congruent

set_option maxHeartbeats 2000000

theorem cyclic_eqangle : ∀ (A B C D : Point) (AB BC CD DA : Line), ( formQuadrilateral A B C D AB BC CD DA) → (A ≠ C) → (∠ D:A:C = ∠ D:B:C) → ∠ C : D : A + ∠ C : B : A = ∟ + ∟ := by
  sorry

end UniGeo.Congruent
