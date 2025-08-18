import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABCD$ be a cyclic quadrilateral. Let $P$, $Q$, $R$ be the feet of the perpendiculars from $D$ to the lines $BC$, $CA$, $AB$, respectively. Show that $PQ=QR$ if and only if the bisectors of $\angle ABC$ and $\angle ADC$ are concurrent with $AC$.
theorem IMO_2003_P4 :
  ∀ (A B C D P Q R X : Point) (BC CA AB : Line),
    cyclic A B C D ∧
    distinctPointsOnLine B C BC ∧
    distinctPointsOnLine C A CA ∧
    distinctPointsOnLine A B AB ∧
    foot D P BC ∧
    foot D Q CA ∧
    foot D R AB →
  (|(P─Q)| = |(Q─R)| ↔ ∃ X : Point, X.onLine CA ∧ ∠A:B:X = ∠X:B:C ∧ ∠A:D:X = ∠X:D:C) := by
  sorry
