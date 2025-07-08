import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--To perpBisector
theorem perpBisector_perpLine : ∀(A B: Point) (AB L: Line), distinctPointsOnLine A B AB ∧  (perpBisector A B L) → perpLine AB L := by
  euclid_intros
  euclid_apply (perpBisector_equiv A B L).mp as (P,L2)
  euclid_finish
--Two circles $G_1$ and $G_2$ intersect at two points $M$ and $N$. Let $AB$ be the line tangent to these circles at $A$ and $B$, respectively, so that $M$ lies closer to $AB$ than $N$. Let $CD$ be the line parallel to $AB$ and passing through the point $M$, with $C$ on $G_1$ and $D$ on $G_2$. Lines $AC$ and $BD$ meet at $E$; lines $AN$ and $CD$ meet at $P$; lines $BN$ and $CD$ meet at $Q$. Show that $EP = EQ$.
theorem IMO_2000_P1 :
  ∀ (M N A B C D E P Q O1 O2 : Point) (G1 G2 : Circle) (AB CD AC BD AN BN : Line),
    circlesIntersectsAtTwoPoints G1 G2 M N ∧
    distinctPointsOnLine A B AB ∧
    tangentAtPoint A O1 AB G1 ∧
    tangentAtPoint B O2 AB G2 ∧
    ¬ AB.intersectsLine CD ∧
    distinctPointsOnLine M C CD ∧
    C.onCircle G1 ∧ C ≠ M ∧ C ≠ N ∧
    D.onCircle G2 ∧ between C M D ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine B D BD ∧
    between E A C ∧ between E B D ∧
    distinctPointsOnLine A N AN ∧
    twoLinesIntersectAtPoint AN CD P ∧
    distinctPointsOnLine B N BN ∧
    twoLinesIntersectAtPoint BN CD Q →
    |(E─P)| = |(E─Q)| := by
    euclid_intros
    euclid_apply line_from_points M N as MN
    euclid_apply intersection_lines MN AB as T
    have midP_ATB: midpoint A T B := by
      sorry
    have midP_PMQ : midpoint P M Q := by
      sorry
    euclid_apply line_from_points E M as EM
    have h_congr: congruentTriangle A B E A B M := by
      have h1: ∠E:A:B = ∠M:A:B := by
        have h2: ∠E:A:B = ∠E:C:D := by
          euclid_apply parallel_eqAlternateExteriorAngle B A D C E AB CD AC
          euclid_finish
        have h3: ∠M:A:B = ∠M:C:A := by
          euclid_apply line_from_points A M as AM
          have h4: M.sameSide B AC := by
            euclid_finish
          euclid_apply inscribedAngle_eq_tangentAngle A M C B O1 G1 AM CD AC AB
          euclid_finish
        euclid_finish
      have h5: ∠E:B:A = ∠M:B:A := by
        have h6: ∠E:B:A = ∠E:D:C := by
          euclid_apply parallel_eqAlternateExteriorAngle A B C D E AB CD BD
          euclid_finish
        have h7: ∠M:B:A = ∠M:D:B := by
          euclid_apply line_from_points B M as BM
          have h8: M.sameSide A BD := by
            euclid_finish
          euclid_apply inscribedAngle_eq_tangentAngle B M D A O2 G2 BM CD BD AB
          euclid_finish
        euclid_finish
      euclid_apply congruent_ASA A B E A B M
      euclid_finish
    have perp_EM_CD: perpLine EM CD := by
      have h1: perpBisector E M AB := by
        euclid_apply perpBisector_construction E M A B AB
        euclid_finish
      euclid_apply perpBisector_perpLine E M EM AB
      euclid_apply perpLine_parallel_perpLine AB EM CD
      euclid_finish
    have perpB: perpBisector P Q EM := by
      euclid_apply (perpBisector_equiv P Q EM).mpr
      euclid_finish
    euclid_finish
