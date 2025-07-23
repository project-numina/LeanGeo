import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABCD$ be a Cyclic quadrilateral. Let $P$, $Q$, $R$ be the feet of the perpendiculars from $D$ to the lines $BC$, $CA$, $AB$, respectively. Show that $PQ=QR$ if and only if the bisectors of $\angle ABC$ and $\angle ADC$ are Concurrent with $AC$.
theorem IMO_2003_P4 :
  ∀ (A B C D P Q R X : Point) (BC CA AB CD DA: Line),
    Cyclic A B C D ∧
    formQuadrilateral A B C D AB BC CD DA ∧
    distinctPointsOnLine B C BC ∧
    distinctPointsOnLine C A CA ∧
    distinctPointsOnLine A B AB ∧
    Foot D P BC ∧
    Foot D Q CA ∧
    Foot D R AB →
  (|(P─Q)| = |(Q─R)| ↔ ∃ X : Point, X.onLine CA ∧ ∠A:B:X = ∠X:B:C ∧ ∠A:D:X = ∠X:D:C) := by
  sorry
