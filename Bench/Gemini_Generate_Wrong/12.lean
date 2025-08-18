import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--8.4. In a convex quadrilateral $A B C D$, angle $C B D$ is equal to angle $C A B$, and angle $A C D$ is equal to angle $B D A$. Prove that then angle $A B C$ is equal to angle $A D C$.-/
theorem Numina_Geometry_808 :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    (formQuadrilateral A B C D AB BC CD DA) ∧
    (∠C:B:D = ∠C:A:B) ∧
    (∠A:C:D = ∠B:D:A) →
    ∠A:B:C = ∠A:D:C := by
    euclid_intros
    euclid_apply line_from_points A C as AC
    euclid_apply line_from_points B D as BD
    have h_intersect : AC.intersectsLine BD := by
      euclid_finish
    euclid_apply intersection_lines AC BD h_intersect as E
    have h_between_AEC : between A E C := by
      euclid_finish
    have h_between_BED : between B E D := by
      euclid_finish
    have h_tri_ACB : triangle A C B := by
      euclid_finish
    have h_tri_BCE : triangle B C E := by
      euclid_finish
    have h_tri_ACD : triangle A C D := by
      euclid_finish
    have h_tri_ADE : triangle A D E := by
      euclid_finish
    have h_angle_eq1 : ∠A:B:C = ∠B:E:C := by
      have h_comp1 : ∠A:C:B = ∠B:C:E := by
        have hA : ¬ coll A E B := by euclid_finish
        euclid_apply angle_between_transfer A E C B
        euclid_finish
      have h_comp2 : ∠C:A:B = ∠C:B:E := by
        have hB : ∠C:B:E = ∠C:B:D := by
          have hD : ¬ coll B E C := by euclid_finish
          euclid_apply angle_between_transfer D E B C
          euclid_finish
        euclid_finish
      euclid_apply similar_AA A C B B C E
      euclid_finish
    have h_angle_eq2 : ∠A:D:C = ∠A:E:D := by
      have h_comp1 : ∠C:A:D = ∠D:A:E := by
        have hA : ¬ coll C E D := by euclid_finish
        euclid_apply angle_between_transfer C E A D
        euclid_finish
      have h_comp2 : ∠A:C:D = ∠A:D:E := by
        have hB : ∠A:D:E = ∠A:D:B := by
          have hD : ¬ coll B E A := by euclid_finish
          euclid_apply angle_between_transfer B E D A
          euclid_finish
        euclid_finish
      euclid_apply similar_AA A C D A D E
      euclid_finish
    have h_vertical : ∠B:E:C = ∠A:E:D := by
      euclid_apply opposite_angles_same A D E B C
      euclid_finish
    euclid_finish
