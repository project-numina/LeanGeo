import SystemE
import UniGeo.Relations
import UniGeo.Abbre
set_option maxHeartbeats 50000000

theorem cyclic_eqangle : ∀ (A B C D : Point) (AB BC CD DA : Line), (formQuadrilateral A B C D AB BC CD DA) → (A ≠ C) → (∠ D:A:C = ∠ D:B:C) → ∠ C : B : A + ∠ C : D : A = ∟ + ∟ := by
  euclid_intros
  euclid_apply (cyclic_judge A B C D AB BC CD DA) as P
  euclid_apply (cyclic_property A B C D AB BC CD DA)
  euclid_finish

#check cyclic_judge
