import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem orthocenter_power_property:
  ∀ (A B C D E F H : Point) (AB BC CA : Line),
    acuteTriangle A B C ∧
    orthoCentre H A B C D E F AB BC CA
    → |(A─H)| * |(H─D)| = |(B─H)| * |(H─E)| := by
    euclid_intros
    -- From the definition of an orthocenter, we get the foot and collinearity properties.
    have h_foot_D : foot A D BC := by euclid_finish
    have h_foot_E : foot B E CA := by euclid_finish
    have h_coll_AHD : coll A H D := by euclid_finish
    have h_coll_BHE : coll B H E := by euclid_finish

    -- For an acute triangle, the feet of the altitudes lie between the vertices of the side.
    have h_D_between : between B D C := by
      euclid_apply acute_triangle_foot_between A B C D BC
      euclid_finish
    have h_E_between : between A E C := by
      euclid_apply acute_triangle_foot_between B A C E CA
      euclid_finish

    -- The foot definition implies right angles.
    have h_angle_ADB : ∠ A:D:B = ∟ := by euclid_finish
    have h_angle_AEB : ∠ A:E:B = ∟ := by euclid_finish

    -- Construct a circle with diameter AB.
    have h_A_neq_B: A ≠ B := by euclid_finish
    euclid_apply exists_midpoint A B as M
    euclid_apply circle_from_points M A as Ω
    have h_diam: diameter A B M Ω := by euclid_finish

    -- Prove that D and E lie on this circle using the property that an angle in a semicircle is a right angle.
    have h_D_on_circle : D.onCircle Ω := by
      euclid_apply rightAngle_diameter_onCircle A B D M Ω
      euclid_finish
    have h_E_on_circle : E.onCircle Ω := by
      euclid_apply rightAngle_diameter_onCircle A B E M Ω
      euclid_finish

    -- Now we know that A, B, D, E are concyclic.
    have h_A_on_circle : A.onCircle Ω := by euclid_finish
    have h_B_on_circle : B.onCircle Ω := by euclid_finish

    -- We need to prove that H lies between the vertices and feet on the altitudes.
    -- In an acute triangle, the orthocenter H lies inside the triangle.
    have h_between_AHD : between A H D := by euclid_finish
    have h_between_BHE : between B H E := by euclid_finish

    -- The points A, D, B, E must be distinct for the intersecting chord theorem.
    -- This follows from the acute triangle property.
    have h_distinct_ADBE : distinctFourPoints A D B E := by euclid_finish

    -- The chords AD and BE of circle Ω intersect at H.
    -- By the intersecting chords theorem (power of a point), we have the desired equality.
    -- The points in `intersecting_chord` map as follows: A->A, B->D, C->B, D->E, E->H.
    euclid_apply intersecting_chord A D B E H Ω
    euclid_finish