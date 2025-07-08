import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Circle
import LeanGeo.Theorem.CirclePosition
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Area
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.Construction
import LeanGeo.Theorem.Parallel
import LeanGeo.Theorem.Trigonometry

open LeanGeo Real
namespace LeanGeo

theorem triangle_two_foot_intersects : ∀ (A B C D E : Point) (AB BC CA AD BE: Line), formTriangle A B C AB BC CA ∧ foot A D BC ∧ foot B E CA ∧ distinctPointsOnLine A D AD ∧ distinctPointsOnLine B E BE → AD.intersectsLine BE := by
  euclid_intros
  by_contra
  euclid_assert perpLine AD BC
  euclid_apply perpLine_parallel_perpLine AD BC BE
  euclid_apply perpLine_parallel_perpLine BE CA AD
  euclid_assert ∠E:B:C = ∟
  by_cases E = C
  · euclid_finish
  · euclid_apply triangle_angleSum E B C
    euclid_apply triangle_anglePositive E B C
    euclid_finish

theorem foot_unique: ∀ (c h g: Point) (AB : Line), foot c h AB ∧ foot c g AB → h = g := by
  euclid_intros
  by_contra
  have h1: ∠c:h:g = ∟ := by
    euclid_finish
  have h2: ∠c:g:h = ∟ := by
    euclid_finish
  have h3: triangle c g h := by
    euclid_finish
  euclid_apply triangle_angleSum c g h
  euclid_apply triangle_anglePositive c g h
  euclid_finish

theorem two_foot_cyclic : ∀ (A B C D E : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ foot A D BC ∧ foot B E CA → |(C─D)| * |(C─B)| =|(C─E)| * |(C─A)|:=  by
  euclid_intros
  by_cases ∠B:C:A = ∟
  · have h1: (E = C) ∧ (D = C) := by
      euclid_apply foot_unique B C E CA
      euclid_apply foot_unique A C D BC
      euclid_finish
    euclid_finish
  · have h2: ∠ A:C:D = ∠B:C:E := by
      by_cases ∠B:C:A < ∟
      · euclid_apply acute_angle_foot_equal A C B D BC
        euclid_apply acute_angle_foot_equal B C A E CA
        euclid_finish
      · have h3: between B C D := by
          euclid_apply obtuse_triangle_foot_between A C B D BC
          euclid_finish
        have h4: between A C E := by
          euclid_apply obtuse_triangle_foot_between B C A E CA
          euclid_finish
        have h5: ∠ A:C:D + ∠A:C:B = ∟ + ∟ := by
          euclid_apply angle_between_transfer
          euclid_finish
        have h6: ∠ B:C:E + ∠B:C:A = ∟ + ∟ := by
          euclid_apply angle_between_transfer
          euclid_finish
        euclid_finish
    euclid_apply similar_AA D C A E C B
    euclid_finish

--Slow in Ceva_inverse
theorem exists_orthocenter: ∀ (A B C D E F: Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ foot A D BC ∧ foot B E CA ∧ foot C F AB → ∃ (H : Point), orthoCentre H A B C D E F AB BC CA:= by
  euclid_intros
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points B E as BE
  euclid_apply triangle_two_foot_intersects A B C D E AB BC CA AD BE
  euclid_apply intersection_lines AD BE as H
  use H
  have h1: |(A─F)| * |(B─D)| * |(C─E)| = |(B─F)| * |(C─D)| * |(A─E)| := by
    have h11: |(C─D)| * |(C─B)| =|(C─E)| * |(A─C)| := by
      euclid_apply two_foot_cyclic A B C D E AB BC CA
      euclid_finish
    have h12: |(A─E)| * |(A─C)| =|(A─F)| * |(B─A)| := by
      euclid_apply two_foot_cyclic B C A E F BC CA AB
      euclid_finish
    have h13: |(B─F)| * |(B─A)| =|(B─D)| * |(C─B)| := by
      euclid_apply two_foot_cyclic C A B F D CA AB BC
      euclid_finish
    have h14: |(C─D)| * |(C─B)| * (|(A─E)| * |(A─C)|) * (|(B─F)| * |(B─A)|) = |(C─E)| * |(A─C)| * |(A─F)| * |(B─A)| * |(B─D)| * |(C─B)| := by
      rw[h11,h12,h13]
      linarith
    have h15: |(A─F)| * |(B─D)| * |(C─E)| * (|(C─B)| * |(A─C)| * |(B─A)|) = |(B─F)| * |(C─D)| * |(A─E)| * (|(C─B)| * |(A─C)| * |(B─A)|):=  by
      calc
      _ = |(C─D)| * |(C─B)| * (|(A─E)| * |(A─C)|) * (|(B─F)| * |(B─A)|)  := by linarith
      _ = |(C─E)| * |(A─C)| * |(A─F)| * |(B─A)| * |(B─D)| * |(C─B)|  := by rw [h14]
      _ = _ := by linarith
    have h_nonzero: (|(C─B)| * |(A─C)| * |(B─A)|) ≠ 0 := by euclid_finish
    apply (mul_left_inj' h_nonzero).mp
    linarith
  have h2: coll C H F := by
    euclid_apply Ceva_inverse B C A E F D H
    euclid_finish
  euclid_finish

theorem rightTriangle_orthocenter:
  ∀ (A B C H D E F : Point) (AB BC CA : Line),
    rightTriangle A B C →
    orthoCentre H A B C D E F AB BC CA →
    H = A := by
  euclid_intros
  have h1: (E = A) ∧ (F = A) := by
      euclid_apply foot_unique B A E CA
      euclid_apply foot_unique C A F AB
      euclid_finish
  euclid_finish

theorem acuteTriangle_orthocenter:
  ∀ (A B C H D E F : Point) (AB BC CA: Line),
    (formAcuteTriangle A B C AB BC CA) ∧ (orthoCentre H A B C D E F AB BC CA)
    → insideTriangle H A B C AB BC CA := by
  euclid_intros
  -- An acute triangle has all angles less than a right angle.
  -- The orthocenter H is the intersection of the altitudes AD, BE, CF.
  -- To prove H is inside triangle ABC, we must show H lies on the same side of each side as the opposite vertex.
  -- This is equivalent to showing that H lies on the interior segments of the altitudes, i.e., between A and D, B and E, and C and F.

  -- First, because the triangle is acute, the feet of the altitudes (D, E, F) lie between the vertices on each side.
  have h_between_BDC : between B D C := by
    euclid_apply acute_triangle_foot_between A B C D BC
    euclid_finish
  have h_between_AEC : between A E C := by
    euclid_apply acute_triangle_foot_between B C A E CA
    euclid_finish
  have h_between_AFB : between A F B := by
    euclid_apply acute_triangle_foot_between C A B F AB
    euclid_finish
  euclid_finish


theorem foot_coll_foot: ∀ (A B H : Point) (l : Line), (foot A H l) ∧ (coll A B H) ∧ (B ≠ H) → foot B H l := by
  euclid_intros
  sorry

theorem orthocenter_transfer : ∀(A B C D E F: Point) (AH BH: Line), distinctPointsOnLine A H AH ∧ distinctPointsOnLine B H BH ∧ orthoCentre H A B C D E F AB BC CA → orthoCentre C A B H E D F AB BH AH:= by
  euclid_intros
  by_cases acuteTriangle A B C
  · have h1 : insideTriangle H A B C AB BC CA := by
      euclid_apply acuteTriangle_orthocenter A B C H D E F AB BC CA
      euclid_finish
    constructor
    · euclid_finish
    constructor
    · euclid_finish
    constructor
    · euclid_finish
    constructor
    · sorry
    · sorry
  · sorry

theorem power_of_orthocenter :
  ∀ (A B C D E F H : Point) (AB BC CA : Line),
    orthoCentre H A B C D E F AB BC CA
    → |(A─H)| * |(H─D)| = |(B─H)| * |(H─E)|  := by
  sorry
