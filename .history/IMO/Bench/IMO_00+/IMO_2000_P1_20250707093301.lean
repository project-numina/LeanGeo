import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0
--To circle
theorem secant_tangent_theorem':∀ (P A B C O: Point) (Ω: Circle)(L:Line), A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ B ≠ C ∧ coll P B C ∧ distinctPointsOnLine P A L ∧ tangentAtPoint A O L Ω → |(P─A)| * |(P─A)| = |(P─B)| * |(P─C)| := by
  euclid_intros
  have h1: P.outsideCircle Ω := by
    euclid_apply tangentLine_outsideCircle A P O Ω L
    euclid_finish
  have h2: between P B C ∨ between P C B := by
    euclid_finish
  rcases h2 with h3|h4
  · euclid_apply secant_tangent_theorem P A B C O Ω L
    euclid_finish
  · euclid_apply secant_tangent_theorem P A C B O Ω L
    euclid_finish

--To perpBisector
theorem perpBisector_perpLine : ∀(A B: Point) (AB L: Line), distinctPointsOnLine A B AB ∧  (perpBisector A B L) → perpLine AB L := by
  euclid_intros
  euclid_apply (perpBisector_equiv A B L).mp as (P,L2)
  euclid_finish

--To Triangle
theorem triangle_para_similar : ∀ (A B C D E: Point) (BC DE : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine D E DE ∧ ¬ BC.intersectsLine DE ∧ coll A B D ∧ coll A C E → similarTriangle A B C A D E := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A C as AC
  have h1: between A D B ∨ between A B D ∨ between B A D ∨ D = B := by
    euclid_finish
  rcases h1 with h2|h3|h4|h5
  · euclid_apply parallel_eqAlternateExteriorAngle E D C B A DE BC AB
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_apply parallel_eqAlternateExteriorAngle C B E D A BC DE AB
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_apply parallel_eqAlternateAngles BC DE AB B D C E
    have h6: ∠ E:A:D = ∠B:A:C := by
      euclid_apply opposite_angles_same D E A C B
      euclid_finish
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_finish

theorem triangle_para_sameRatio: ∀ (A B C D E F G: Point) (BC DE : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine D E DE ∧ ¬ BC.intersectsLine DE ∧ coll A B D ∧ coll A C E ∧ F.onLine BC ∧ G.onLine DE ∧ coll A G F ∧ F ≠ B ∧ F ≠ C ∧ G ≠ D ∧ G ≠ E → |(D─G)| * |(B─C)|  =|(D─E)| *|(B─F)| := by
  euclid_intros
  euclid_apply triangle_para_similar A B C D E BC DE
  euclid_apply triangle_para_similar A B F D G BC DE
  have h1: |(D─G)| * |(A─B)| = |(B─F)| * |(A─D)| := by
    euclid_finish
  have h2: |(D─E)| * |(A─B)| = |(B─C)| * |(A─D)| := by
    euclid_finish
  have h3: |(A─B)| * |(A─D)| > 0 := by
    euclid_finish
  have h5: |(D─G)| * |(B─C)| * (|(A─B)| * |(A─D)|) =|(D─E)| * |(B─F)| * (|(A─B)| * |(A─D)|) := by
    calc
      _ = (|(D─G)| * |(A─B)|) * (|(B─C)| * |(A─D)|) := by linarith
      _ = (|(B─F)| * |(A─D)|) * (|(D─E)| * |(A─B)|) := by rw[h1,h2]
      _ = _ := by linarith
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
      have h1: |(T─A)| * |(T─A)| = |(T─M)| * |(T─N)| := by
        euclid_apply secant_tangent_theorem' T A M N O1 G1 AB
        euclid_finish
      have h2: |(T─B)| * |(T─B)| = |(T─M)| * |(T─N)| := by
        euclid_apply secant_tangent_theorem' T B M N O2 G2 AB
        euclid_finish
      have h3: |(T─A)| * |(T─A)| = |(T─B)| * |(T─B)| := by
        rw[h1,h2]
      euclid_assert |(T─A)| > 0
      euclid_assert |(T─B)| > 0
      have h4: |(T─A)| = |(T─B)| := by
        nlinarith
      euclid_finish
    have midP_PMQ : midpoint P M Q := by
      euclid_apply triangle_para_sameRatio N T A M P B Q AB CD
      have h1 : |(M─Q)| = |(M─P)| := by
        have h4: |(T─A)| = |(T─B)| := by euclid_finish
        euclid_finish
      have h2: between P M Q := by
        euclid_finish
      euclid_finish
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
