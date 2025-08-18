import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--
**Apollonius's Theorem**. In a triangle $A B C$, if $D$ is the midpoint of the side $B C$, then the sum of the squares of the sides $A B$ and $A C$ is equal to twice the sum of the squares of the median $A D$ and half the base $B D$.
That is, $|(A-B)|^2 + |(A-C)|^2 = 2 (|(A-D)|^2 + |(B-D)|^2)$.
-/

lemma point_on_line_second_order_equation: ∀ (B C D H: Point),B ≠ C ∧  midpoint B D C ∧ coll B C H →
|(H─B)| * |(H─B)| + |(H─C)| * |(H─C)| = 2 * (|(H─D)| * |(H─D)| + |(B─D)| * |(B─D)|) := by
  euclid_intros
  -- The claim is an algebraic identity about distances of collinear points.
  -- The proof proceeds by case analysis on the position of H relative to B and C.
  -- We are given `coll B C H`, which is a disjunction. We can use `cases` on it.
  have h_coll : between B C H ∨ between C H B ∨ between H B C ∨ B = H ∨ C = H := by
    euclid_finish
  rcases h_coll with h_BCH | h_CHB | h_HBC | h_eq_B | h_eq_C
  · -- Case 1: `between B C H`.
    -- This implies the order of points is B-D-C-H, since D is the midpoint of BC.
    -- We express |(H─B)| and |(H─C)| in terms of |(H─D)| and |(B─D)|.
    have h1: |(H─B)| = |(H─D)| + |(B─D)| := by euclid_finish
    have h2: |(H─C)| = |(H─D)| - |(C─D)| := by euclid_finish
    -- Now substitute these into the goal. The SMT solver can verify the algebraic identity.
    euclid_finish
  · -- Case 2: `between C H B`, which is equivalent to `between B H C`.
    -- In this case, H lies on the segment BC.
    -- D is the midpoint of BC. Thus H is either between B and D, on D, or between D and C.
    by_cases h_HD: H = D
    · -- Subcase H = D.
      euclid_finish
    · -- Subcase H ≠ D.
      have h_trichotomy : between B H D ∨ between B D H := by
        euclid_apply line_from_points B C as BC
        euclid_finish
      rcases h_trichotomy with h_BHD | h_BDH
      · -- Subcase `between B H D`. The order is B-H-D-C.
        have h1: |(H─B)| = |(B─D)| - |(H─D)| := by euclid_finish
        have h2: |(H─C)| = |(C─D)| + |(H─D)| := by euclid_finish
        euclid_finish
      · -- Subcase `between B D H`. The order is B-D-H-C.
        have h1: |(H─B)| = |(B─D)| + |(H─D)| := by euclid_finish
        have h2: |(H─C)| = |(C─D)| - |(H─D)| := by euclid_finish
        euclid_finish
  · -- Case 3: `between H B C`.
    -- This implies the order of points is H-B-D-C.
    have h1: |(H─B)| = |(H─D)| - |(B─D)| := by euclid_finish
    have h2: |(H─C)| = |(H─D)| + |(C─D)| := by euclid_finish
    euclid_finish
  · -- Case 4: `H = B`.
    euclid_finish
  · -- Case 5: `H = C`.
    euclid_finish

theorem Apollonius_Theorem :
  ∀ (A B C D : Point),
    triangle A B C ∧
    midpoint B D C
    → |(A─B)| * |(A─B)| + |(A─C)| * |(A─C)| = 2 * (|(A─D)| * |(A─D)| + |(B─D)| * |(B─D)|) := by
    -- Introduce all variables and hypotheses into the context.
    euclid_intros
    -- Construct the line BC, since B and C are distinct points (from `triangle A B C`).
    euclid_apply line_from_points B C as BC
    -- To drop a perpendicular from A to BC, we must first prove A is not on line BC.
    have h_A_not_on_BC : ¬(A.onLine BC) := by
      -- This follows directly from the definition of a triangle (A, B, C are not collinear).
      euclid_apply point_not_onLine A B C BC
      euclid_finish
    -- Construct the foot of the perpendicular from A to the line BC, let's call it H.
    euclid_apply exists_foot A BC as H
    -- Now we apply the Pythagorean theorem to the right-angled triangles formed by H.
    -- We must handle the cases where H coincides with B, C, or D.

    -- First, establish the Pythagorean relationship for ΔAHB.
    have h_pyth_AB : |(A─B)| * |(A─B)| = |(A─H)| * |(A─H)| + |(H─B)| * |(H─B)| := by
      -- Consider the case where the foot H is the same point as B.
      by_cases h_HB : H = B
      · -- In this case, the triangle ABC is a right-angled triangle at B.
        -- |(H-B)| is zero, and the identity becomes |(A-B)|^2 = |(A-B)|^2, which is trivial.
        euclid_assert |(H─B)| = 0
        euclid_finish
      · -- If H and B are distinct, ΔAHB is a right-angled triangle at H.
        have h_rt_HAB : rightTriangle H A B := by
          -- The non-collinearity of H, A, B is guaranteed because A is not on line BC.
          -- The right angle at H is from the definition of the foot.
          euclid_finish
        -- Apply the Pythagorean theorem.
        euclid_apply pythagorean_point H A B
        -- The SMT solver can now conclude the desired equality.
        euclid_finish

    -- Second, establish the Pythagorean relationship for ΔAHC.
    have h_pyth_AC : |(A─C)| * |(A─C)| = |(A─H)| * |(A─H)| + |(H─C)| * |(H─C)| := by
      -- This proof is symmetric to the one for ΔAHB.
      by_cases h_HC : H = C
      · euclid_assert |(H─C)| = 0
        euclid_finish
      · have h_rt_HAC : rightTriangle H A C := by
          euclid_finish
        euclid_apply pythagorean_point H A C
        euclid_finish

    -- Third, establish the Pythagorean relationship for ΔAHD.
    have h_pyth_AD : |(A─D)| * |(A─D)| = |(A─H)| * |(A─H)| + |(H─D)| * |(H─D)| := by
      -- This proof is also similar, considering whether H coincides with D.
      by_cases h_HD : H = D
      · euclid_assert |(H─D)| = 0
        euclid_finish
      · have h_rt_HAD : rightTriangle H A D := by
          euclid_finish
        euclid_apply pythagorean_point H A D
        euclid_finish
    -- Finally, with all the necessary Pythagorean identities established,
    -- along with the properties of a midpoint (`between B D C`, `|(B-D)| = |(D-C)|`)
    -- and the collinearity of B, D, C, H, the SMT solver can solve the algebraic goal.
    rw[h_pyth_AB, h_pyth_AC, h_pyth_AD]
    have h_line: |(H─B)| * |(H─B)| + |(H─C)| * |(H─C)| = 2 * (|(H─D)| * |(H─D)| + |(B─D)| * |(B─D)|) := by
      euclid_apply point_on_line_second_order_equation
      euclid_finish
    linarith
