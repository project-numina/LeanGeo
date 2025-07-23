import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem parallelogram_transversal_property:
  ∀ (A B C D E F : Point) (AB AD BC CD CEFD : Line),
    Parallelogram A B C D AB AD BC CD ∧
    distinctThreePointsOnLine C E F CEFD ∧
    E.onLine AB ∧ F.onLine AD ∧ A ≠ E ∧ A ≠ F ∧
    between A B E ∧ between A D F
    → |(A─B)| * |(A─F)| + |(A─D)| * |(A─E)| = |(A─E)| * |(A─F)| := by
  euclid_intros
  -- From the definition of a parallelogram, sides BC and AD are parallel.
  -- Since F lies on the line AD, BC is also parallel to AF.
  have h_BC_parallel_AF : ¬ BC.intersectsLine AD := by
    euclid_finish

  -- Also, in a parallelogram, opposite sides are equal in length.
  have h_AD_eq_BC : |(A─D)| = |(B─C)| := by
    euclid_apply parallelogram_imp_eq_opposite_sides A B C D AB AD BC CD
    euclid_finish

  -- We establish that ΔEBC is similar to ΔEAF.
  -- This follows from the AA similarity criterion.
  have h_tri_EBC_similar_EAF : SimilarTriangles E B C E A F := by
    -- First, we need to ensure that E, B, C and E, A, F form non-degenerate triangles.
    have h_tri_EBC: Triangle E B C := by euclid_finish
    have h_tri_EAF: Triangle E A F := by euclid_finish

    -- Second, we identify two pairs of equal angles.
    -- Angle ∠AEF (same as ∠BEC) is common to both triangles.
    have h_angle_E_common : ∠ B:E:C = ∠ A:E:F := by
      -- This holds because A,B,E are collinear and C,F,E are collinear.
      euclid_finish

    -- Angles ∠EBC and ∠EAF are corresponding angles formed by the parallel lines BC and AF
    -- and the transversal AE. Hence, they are equal.
    have h_corr_angles_eq : ∠ E:B:C = ∠ E:A:F := by
      -- We can prove this from the property that consecutive interior angles are supplementary.
      -- The consecutive interior angles ∠DAB and ∠ABC add up to 180 degrees.
      have h_cons_int_supp : ∠ D:A:B + ∠ A:B:C = ∟ + ∟ := by
        euclid_apply parallel_imp_supp_consecutiveAngles AD BC AB A B D C
        euclid_finish
      -- Angles ∠EBC and ∠ABC are supplementary because A, B, E are collinear.
      have h_on_line_supp : ∠ E:B:C + ∠ A:B:C = ∟ + ∟ := by
        have h_tri_ABC: Triangle A B C := by euclid_finish
        euclid_apply coll_supp_angles C A B E
        euclid_finish
      -- From these two supplementary relations, we get ∠DAB = ∠EBC.
      have h_DAB_eq_EBC : ∠ D:A:B = ∠ E:B:C := by euclid_finish
      -- Since D is between A and F, ray AD is the same as ray AF, so ∠DAB = ∠FAB.
      -- The angle notation ∠X:Y:Z is orientation-independent, so ∠FAB is ∠EAF.
      have h_DAB_eq_EAF : ∠ D:A:B = ∠ E:A:F := by euclid_finish
      -- By transitivity, ∠EBC = ∠EAF.
      euclid_finish

    -- With two pairs of equal angles, the triangles are similar.
    euclid_apply similar_AA E B C E A F
    euclid_finish

  -- From the similarity of triangles, we have the following proportion of side lengths:
  -- |(E─B)| / |(E─A)| = |(B─C)| / |(A─F)|
  -- which can be written as:
  have h_ratio_from_sim: |(E─B)| * |(A─F)| = |(E─A)| * |(B─C)| := by euclid_finish

  -- Since B is between A and E, we have |(A─E)| = |(A─B)| + |(B─E)|.
  have h_between_dist : |(A─E)| = |(A─B)| + |(E─B)| := by euclid_finish

  -- Now we combine these geometric facts to derive the algebraic conclusion.
  -- The SMT solver can solve this system of equations.
  euclid_finish
