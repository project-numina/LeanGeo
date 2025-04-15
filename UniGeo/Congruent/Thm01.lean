import SystemE
import Book.Prop29
import SystemE.Theory.Relations
import UniGeo.Abbre
namespace UniGeo.Congruent

set_option maxHeartbeats 2000000

theorem cyclic_eqangle : ∀ (A B C D : Point) (AB BC CD DA : Line), ( formQuadrilateral A B C D AB BC CD DA) → (A ≠ C) → (∠ D:A:C = ∠ D:B:C) → ∠ C : D : A + ∠ C : B : A = ∟ + ∟ := by
  euclid_intros
  euclid_apply (cyclic_judge A B C D AB BC CD DA) as P
  euclid_apply (cyclic_property A B C D AB BC CD DA)
  euclid_finish

end UniGeo.Congruent
