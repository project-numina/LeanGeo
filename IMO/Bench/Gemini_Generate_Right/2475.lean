import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem angle_altitude_circumradius_equal:
  ∀ (A B C O H : Point) (Ω : Circle) (BC AB AC: Line),
    acuteTriangle A B C ∧
    formTriangle A B C AB BC AC ∧
    circumCircle Ω A B C ∧
    O.isCentre Ω ∧
    -- This condition holds for acute triangles, but we state it to use the given theorem easily
    O.sameSide C AB ∧
    foot A H BC
    → ∠ O:A:B = ∠ H:A:C := by
    euclid_intros
    -- Goal is to prove ∠OAB = ∠HAC.
    -- The strategy is to show that both angles are equal to 90° - ∠ACB.

    -- Part 1: Show ∠HAC = 90° - ∠ACB.
    -- From `acuteTriangle`, we know the foot H of the altitude from A lies between B and C.
    have h_foot_between : between B H C := by
      euclid_apply acute_triangle_foot_between A B C H BC
      euclid_finish
    -- Since A is not on line BC and H,C are, AHC forms a triangle.
    have h_tri_AHC : triangle A H C := by
      euclid_finish
    -- Since AH is an altitude, ∠AHC is a right angle.
    have h_AHC_right : ∠ A:H:C = ∟ := by
      euclid_finish
    -- The angles in a triangle sum to 180°.
    have h_sum_AHC : ∠ H:A:C + ∠ A:C:H + ∠ A:H:C = ∟ + ∟ := by
      euclid_apply triangle_angleSum A H C
      euclid_finish
    -- Since H is between B and C, ∠ACH is the same as ∠ACB.
    have h_angle_eq : ∠ A:C:H = ∠ A:C:B := by
      euclid_apply angle_between_transfer B H C A
      euclid_finish
    -- By substituting the right angle and equal angles, we find ∠HAC = 90° - ∠ACB.
    have h_HAC : ∠ H:A:C = ∟ - ∠ A:C:B := by
      euclid_finish

    -- Part 2: Show ∠OAB = 90° - ∠ACB.
    -- First, in triangle OAB, OA and OB are radii, so the triangle is isosceles.
    have h_OAB_is_iso : isoTriangle O A B := by
      -- O,A,B are not collinear because triangle ABC is acute, so ∠ACB is not 90°.
      have h_tri_oab: triangle O A B := by euclid_finish
      have h_radii_eq: |(O─A)| = |(O─B)| := by euclid_finish
      euclid_finish
    -- In an isosceles triangle, the base angles are equal.
    have h_base_angles_eq : ∠ O:A:B = ∠ O:B:A := by
      euclid_apply isoTriangle_eqAngle O A B
      euclid_finish
    -- Apply the given theorem relating the circumcenter angle and inscribed angle.
    have h_comp_angle : ∠ O:B:A + ∠ A:C:B = ∟ := by
      euclid_apply circumcenter_inscribed_angle_complementary A B C O AB BC AC Ω
      euclid_finish
    -- From the complementary angle relation and the equality of base angles, we get ∠OAB = 90° - ∠ACB.
    have h_OAB : ∠ O:A:B = ∟ - ∠ A:C:B := by
      euclid_finish

    -- From Part 1 and Part 2, both angles are equal to the same value, so they are equal.
    euclid_finish