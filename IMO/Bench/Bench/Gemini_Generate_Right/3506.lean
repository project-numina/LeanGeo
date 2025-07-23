import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem exercise_angle_bisector_lengths :
  ∀ (A B C D: Point),
    Triangle A B C ∧
    ∠B:A:D = ∠C:A:D ∧
    Coll B D C ∧
    between B D C ∧
    |(A─C)| * 2 = |(A─B)| * 3
    → |(B─C)| * 2 = |(B─D)| * 5 := by
  euclid_intros
  -- Apply the Angle Bisector Theorem to Triangle ABC with angle bisector AD.
  -- This adds the proposition `|(A─C)| * |(B─D)| = |(A─B)| * |(C─D)|` to the context.
  euclid_apply AngleBisectorTheorem A B C D
  -- We are given the ratio of the sides AB and AC. Combining this with the
  -- result of the angle bisector theorem, we can establish a ratio between
  -- the segments BD and CD.
  have h_segment_ratio : |(C─D)| * 2 = |(B─D)| * 3 := by
    -- This follows from the context:
    -- 1. |(A─C)| * |(B─D)| = |(A─B)| * |(C─D)| (from AngleBisectorTheorem)
    -- 2. |(A─C)| * 2 = |(A─B)| * 3 (given)
    -- Also, `triangle A B C` implies side lengths are positive, allowing division.
    -- The SMT solver can solve this system of equations.
    euclid_finish
  -- The proposition `between B D C` implies that |(B─C)| = |(B─D)| + |(C─D)|.
  -- The final goal follows from this property and the segment ratio derived above.
  -- |(C─D)| = |(B─D)| * 3 / 2
  -- |(B─C)| = |(B─D)| + |(B─D)| * 3 / 2 = |(B─D)| * (1 + 3/2) = |(B─D)| * 5 / 2
  -- 2 * |(B─C)| = 5 * |(B─D)|
  euclid_finish
