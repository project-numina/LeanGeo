import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--2. Point $K$ is the midpoint of the hypotenuse $AB$ of a right isosceles triangle $ABC$. Points $L$ and $M$ are chosen on the legs $BC$ and $AC$ respectively such that $BL = CM$. Prove that triangle $LMK$ is also a right isosceles triangle.-/
theorem Numina_Geometry_623 :
  ∀ (A B C K L M : Point),
    rightTriangle C A B ∧
    isoTriangle C A B ∧
    midpoint A K B ∧
    between B L C ∧
    between A M C ∧
    |(B─L)| = |(C─M)| →
    rightTriangle K L M ∧
    isoTriangle K L M := by
    euclid_intros
    -- We will prove △MAK ≅ △LCK by SAS.
    euclid_apply line_from_points A C as AC
    euclid_apply line_from_points A B as AB
    euclid_apply line_from_points B C as BC
    euclid_apply line_from_points M K as MK
    euclid_apply line_from_points L K as LK
    euclid_apply line_from_points C K as CK
    -- Side: Prove |(A─K)| = |(C─K)|
    have h_AK_eq_CK : |(A─K)| = |(C─K)| := by
      euclid_apply rightTriangle_midLine_half C A B K
      euclid_finish

    -- Angle: Prove ∠M:A:K = ∠L:C:K
    have h_angles_at_base_45 : ∠ C:A:B = ∟/2 ∧ ∠ C:B:A = ∟/2 := by
      have h_base_angles_eq : ∠ C:A:B = ∠ C:B:A := by
        euclid_apply isoTriangle_eqAngle C A B
        euclid_finish
      have h_angle_sum : ∠ C:A:B + ∠ C:B:A + ∠ A:C:B = ∟ + ∟ := by
        euclid_apply triangle_angleSum C A B
        euclid_finish
      split_ands <;> euclid_finish
    have h_MAK_eq_LCK : ∠ M:A:K = ∠ L:C:K := by
      have h_MAK_45 : ∠ M:A:K = ∟/2 := by
        -- Since K is on AB and M is on AC, ∠MAK is the same as ∠CAB.
        have h_angle_eq_1 : ∠ M:A:K = ∠ C:A:B := by
          euclid_finish
        rw [h_angle_eq_1, h_angles_at_base_45.1]
      have h_LCK_45 : ∠ L:C:K = ∟/2 := by
        -- Since |(K─B)| = |(K─C)|, △KBC is isosceles.
        have h_iso_KBC : isoTriangle K B C := by
            have h_AK_eq_BK : |(A─K)| = |(K─B)| := by euclid_finish
            have h_CK_eq_BK : |(C─K)| = |(K─B)| := by euclid_finish
            have h_tri_KBC : triangle K B C := by
              euclid_apply line_from_points B C as BC
              euclid_finish
            euclid_finish
        have h_KCB_eq_KBC : ∠ K:C:B = ∠ K:B:C := by
          euclid_apply isoTriangle_eqAngle K B C
          euclid_finish
        have h_KBC_45 : ∠ K:B:C = ∟/2 := by euclid_finish
        have h_angle_eq_2 : ∠ L:C:K = ∠ B:C:K := by euclid_finish
        euclid_finish
      rw [h_MAK_45, h_LCK_45]
    -- Side: Prove |(A─M)| = |(L─C)|
    have h_AM_eq_LC : |(A─M)| = |(L─C)| := by
      have h_AC_eq_BC : |(A─C)| = |(B─C)| := by euclid_finish
      have h_AC_sum : |(A─C)| = |(A─M)| + |(M─C)| := by euclid_finish
      have h_BC_sum : |(B─C)| = |(B─L)| + |(L─C)| := by euclid_finish
      euclid_finish
    -- Now apply SAS congruence
    have h_cong_MAK_LCK : congruentTriangle M A K L C K := by
      euclid_apply congruent_SAS M A K L C K
      euclid_finish
    -- From congruence, we can prove the two parts of the goal.
    constructor
    · -- Prove rightTriangle K L M by showing ∠L:K:M = ∟.
      -- First, show ∠A:K:C = ∟.
      have h_AKC_right : ∠ A:K:C = ∟ := by
        have h_iso_KAC : isoTriangle K A C := by euclid_finish
        have h_angle_sum : ∠ A:K:C + ∠ K:A:C + ∠ K:C:A = ∟ + ∟ := by
          euclid_apply triangle_angleSum K A C
          euclid_finish
        have h_KAC_eq_KCA : ∠ K:A:C = ∠ K:C:A := by
          euclid_apply isoTriangle_eqAngle K A C
          euclid_finish
        euclid_finish
      -- From congruence, ∠A:K:M = ∠C:K:L.
      have h_AKM_eq_CKL : ∠ A:K:M = ∠ C:K:L := by euclid_finish
      -- Since M is on AC, ∠AKC = ∠AKM + ∠MKC.
      have h_angle_add_AKC : ∠ A:K:C = ∠ A:K:M + ∠ M:K:C := by
        euclid_apply line_from_points A C as AC
        euclid_apply between_angleSum K A M C
        euclid_finish
      -- The sum ∠LKC + ∠MKC is ∠LKM.
      have h_LKM_add : ∠ L:K:M = ∠ L:K:C + ∠ C:K:M := by
        euclid_finish
      -- Combine these to show ∠LKM = 90.
      have h_LKM_right : ∠ L:K:M = ∟ := by
        euclid_finish
      have h_tri_KLM : triangle K L M := by euclid_finish
      euclid_finish
    · -- Prove isoTriangle K L M.
      -- This follows directly from the congruence `|(K─M)| = |(K─L)|`.
      have h_KM_eq_KL : |(K─M)| = |(K─L)| := by euclid_finish
      have h_tri_KLM : triangle K L M := by euclid_finish
      euclid_finish
