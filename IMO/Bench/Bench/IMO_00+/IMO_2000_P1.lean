import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0
--To circle
--Two circles $G_1$ and $G_2$ intersect at two points $M$ and $N$. Let $AB$ be the line tangent to these circles at $A$ and $B$, respectively, so that $M$ lies closer to $AB$ than $N$. Let $CD$ be the line parallel to $AB$ and passing through the point $M$, with $C$ on $G_1$ and $D$ on $G_2$. Lines $AC$ and $BD$ meet at $E$; lines $AN$ and $CD$ meet at $P$; lines $BN$ and $CD$ meet at $Q$. Show that $EP = EQ$.
theorem IMO_2000_P1 :
  ∀ (M N A B C D E P Q O1 O2 : Point) (G1 G2 : Circle) (AB CD AC BD AN BN : Line),
    CirclesIntersectAtTwoPoints G1 G2 M N ∧
    distinctPointsOnLine A B AB ∧
    TangentLineCircleAtPoint A O1 AB G1 ∧
    TangentLineCircleAtPoint B O2 AB G2 ∧
    ¬ AB.intersectsLine CD ∧
    distinctPointsOnLine M C CD ∧
    C.onCircle G1 ∧ C ≠ M ∧ C ≠ N ∧
    D.onCircle G2 ∧ between C M D ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine B D BD ∧
    between E A C ∧ between E B D ∧
    distinctPointsOnLine A N AN ∧
    TwoLinesIntersectAtPoint AN CD P ∧
    distinctPointsOnLine B N BN ∧
    TwoLinesIntersectAtPoint BN CD Q →
    |(E─P)| = |(E─Q)| := by
    euclid_intros
    euclid_apply line_from_points M N as MN
    euclid_apply intersection_lines MN AB as T
    have midP_ATB: MidPoint A T B := by
      have h1: |(T─A)| * |(T─A)| = |(T─M)| * |(T─N)| := by
        euclid_apply TangentSecantTheorem T A M N O1 G1 AB
        euclid_finish
      have h2: |(T─B)| * |(T─B)| = |(T─M)| * |(T─N)| := by
        euclid_apply TangentSecantTheorem T B M N O2 G2 AB
        euclid_finish
      have h3: |(T─A)| * |(T─A)| = |(T─B)| * |(T─B)| := by
        rw[h1,h2]
      euclid_assert |(T─A)| > 0
      euclid_assert |(T─B)| > 0
      have h4: |(T─A)| = |(T─B)| := by
        nlinarith
      euclid_finish
    have midP_PMQ : MidPoint P M Q := by
      have h1 : |(M─Q)| = |(M─P)| := by
        have h4: |(T─A)| = |(T─B)| := by euclid_finish
        have h5: |(M─Q)| * |(T─A)| = |(M─P)| * |(T─B)| := by
          euclid_apply triangle_parallel_bases_eq_ratio N T A M P B Q AB CD
          euclid_finish
        rw [h4] at h5
        have h6: |(T─B)| > 0 := by euclid_finish
        euclid_finish
      have h2: between P M Q := by
        euclid_finish
      euclid_finish
    euclid_apply line_from_points E M as EM
    have h_congr: CongruentTriangles A B E A B M := by
      have h1: ∠E:A:B = ∠M:A:B := by
        have h2: ∠E:A:B = ∠E:C:D := by
          euclid_apply parallel_imp_eq_alternateExteriorAngles B A D C E AB CD AC
          euclid_finish
        have h3: ∠M:A:B = ∠M:C:A := by
          euclid_apply line_from_points A M as AM
          have h4: M.sameSide B AC := by
            euclid_finish
          euclid_apply AlternateSegmentTheorem A M C B O1 G1 AM CD AC AB
          euclid_finish
        euclid_finish
      have h5: ∠E:B:A = ∠M:B:A := by
        have h6: ∠E:B:A = ∠E:D:C := by
          euclid_apply parallel_imp_eq_alternateExteriorAngles A B C D E AB CD BD
          euclid_finish
        have h7: ∠M:B:A = ∠M:D:B := by
          euclid_apply line_from_points B M as BM
          have h8: M.sameSide A BD := by
            euclid_finish
          euclid_apply AlternateSegmentTheorem B M D A O2 G2 BM CD BD AB
          euclid_finish
        euclid_finish
      euclid_apply congruentTriangles_ASA A B E A B M
      euclid_finish
    have perp_EM_CD: PerpLine EM CD := by
      have h1: PerpBisector E M AB := by
        euclid_apply perpBisector_if_eq_dist E M A B AB
        euclid_finish
      euclid_apply perpBisector_imp_perpLine E M EM AB
      euclid_apply perp_parallel_imp_perp AB EM CD
      euclid_finish
    have perpB: PerpBisector P Q EM := by
      euclid_apply (perpBisector_iff P Q EM).mpr
      euclid_finish
    euclid_finish
