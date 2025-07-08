import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import Book

open Elements.Book1

open LeanGeo
namespace LeanGeo
theorem construct_perpBisector' (a b : Point) : (a ≠ b) →  ∃ L, perpBisector a b L ∧ ∃ M : Point, M.onLine L ∧ midpoint a M b := by
  intro hab
  obtain ⟨AB, ha, hb⟩ := line_from_points a b hab
  euclid_apply (proposition_1 a b AB) as c
  euclid_apply (line_from_points c a) as AC
  euclid_apply (line_from_points c b ) as BC
  euclid_apply (proposition_9' c a b AC BC) as d'
  euclid_apply (line_from_points c d') as CD
  use CD
  have crux : perpBisector a b CD := by
    use hab
    intro x hx
    cases em (c = x) with
    | inl hl =>
      rw [← hl]
      euclid_finish
    | inr hr =>
      obtain ⟨AX, ha', hx⟩ := line_from_points a x (by euclid_finish)
      obtain ⟨XC, hx', hc'⟩ := line_from_points x c (fun a => hr (id (Eq.symm a)))
      obtain  ⟨BX, hx'', hb'⟩ := line_from_points b x (by euclid_finish)
      have : ∠ a:c:x = ∠ b:c:x := by
        have : x.sameSide d' AC ∧ x.sameSide d' BC ∨ x.opposingSides d' AC ∧ x.opposingSides d' BC := by euclid_finish
        cases this with
        | inl hrl => euclid_finish
        | inr hrr =>
          have : ∠ a:c:x + ∠ a:c:d' = ∟ + ∟ := by
            apply supplementaryAngle_line
            euclid_finish
          have : ∠ b:c:x + ∠ b:c:d' = ∟ + ∟ := by
            apply supplementaryAngle_line
            euclid_finish
          euclid_finish
      euclid_apply proposition_4 c a x c b x AC AX XC BC BX XC
      euclid_finish
  apply And.intro
  · tauto
  · euclid_apply (intersection_lines CD AB) as d
    use d
    euclid_finish

theorem construct_perpBisector (a b : Point) : (a ≠ b) →  ∃ L, perpBisector a b L := by
  intro hab
  obtain ⟨L, hL⟩ := construct_perpBisector' a b hab
  use L
  exact hL.1

theorem centre_if_equidistant (a b c o : Point) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (C : Circle) (ha : a.onCircle C) (hb : b.onCircle C) (hc : c.onCircle C) : |(o─a)| = |(o─b)| ∧ |(o─b)| = |(o─c)| → o.isCentre C := by sorry

theorem exists_centre : ∀ (O: Circle), ∃ (C : Point), C.isCentre O := by
  euclid_intros
  obtain ⟨A, hA⟩ : ∃ A : Point, A.onCircle O := exists_point_on_circle O
  obtain ⟨B, hAB, hB⟩ := exists_distinct_point_on_circle O A
  obtain ⟨AB, hAB1, hAB2⟩ := line_from_points A B hAB.symm
  obtain ⟨L, ⟨hL, M, hM⟩⟩ := construct_perpBisector' A B hAB.symm
  have : M.insideCircle O := by euclid_finish
  have := intersection_circle_line_2 M O L (by euclid_finish)
  obtain ⟨C1, C2, hC11, hC12, hC21, hC22, hC1C2⟩ := intersections_circle_line O L this
  obtain ⟨L', ⟨hL',M', hM'⟩⟩ := construct_perpBisector' C1 B (by euclid_finish)
  obtain ⟨C1B, hC1, hB⟩ := line_from_points C1 B (by euclid_finish)
  have : L'.intersectsLine L := by
    apply by_contra
    intro hh
    -- have : ∠ B:C1:M < ∟ := by euclid_finish
    sorry
  obtain ⟨E, hE⟩ := intersection_lines L' L this
  use E
  have := centre_if_equidistant
  euclid_finish

theorem exists_midpoint : ∀ (A B : Point), A ≠ B → ∃(P : Point), midpoint A P B := by
  intro A B h
  obtain ⟨AB, hA, hB⟩ := line_from_points A B h
  obtain ⟨L, hL⟩ := construct_perpBisector' A B h
  obtain ⟨M, hM1, hM2⟩ := intersection_lines AB L (by euclid_finish)
  use M
  euclid_finish

--theorem exists_foot : ∀ (A : Point) (l : Line), ∃(P : Point), P.onLine l ∧
--(∀ Q:Point, Q.onLine l → ∠A:P:Q = ∟) := by
--  sorry
theorem midpoint_twice: ∀ (A B P : Point), midpoint A P B → |(A─B)| * 1/2 = |(P─B)|  := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish


#check between_points

theorem exists_foot : ∀ (c: Point) (AB : Line),
   ¬(c.onLine AB) →
  ∃ h : Point, foot c h AB :=
by
  intro P AB hh
  obtain ⟨A, hA⟩ := line_nonempty AB
  obtain ⟨B, hAB, hB⟩ := exists_distincts_points_on_line AB A
  obtain ⟨h, Hh1, Hh2⟩ := proposition_12 A B P AB (by euclid_finish)
  use h
  wlog q : ∠ A:h:P = ∟ with H
  · have : ∠ B:h:P = ∟ := by tauto
    exact H P AB hh B (by tauto) A (by tauto) (by tauto) h Hh1 (by tauto) this
  use (by euclid_finish)
  use (by euclid_finish)
  intro x hx
  have : h ≠ A ∨ h ≠ B := by euclid_finish
  cases this with
  | inl hl =>
    have : between x A h ∨ between A x h ∨ between A h x ∨ x = A := by euclid_finish
    rcases this with hh | hh | hh | hh | hh
    · have : ∠ x:h:P = ∠ A:h:P := by
        have : ¬ coll P x h := by euclid_finish
        sorry
      euclid_finish
    · have : ∠ x:h:P = ∠ A:h:P := by sorry
      euclid_finish
    · have : ∠ x:h:P + ∠ A:h:P = ∟ + ∟ := by sorry
      euclid_finish
    · euclid_finish
  | inr hr =>
    have : ∠ A:h:P + ∠ P:h:B = ∟ + ∟ := by sorry
    have : between x B h ∨ between B x h ∨ between B h x ∨ x = B := by euclid_finish
    rcases this with hh | hh | hh | hh | hh
    · have : ∠ x:h:P = ∠ B:h:P := by sorry
      euclid_finish
    · have : ∠ x:h:P = ∠ B:h:P := by sorry
      euclid_finish
    · have : ∠ x:h:P + ∠ B:h:P = ∟ + ∟ := by sorry
      euclid_finish
    · euclid_finish

theorem exists_angleBisection : ∀ (A B C : Point),
(A ≠ B) ∧ (A ≠ C) ∧ ¬(coll A B C)
→ ∃ (L : Line), ∀ (P: Point), P.onLine L ↔ ∠ A:B:P = ∠ P:B:C
:= by
  euclid_intros
  obtain ⟨AB, hA, hB⟩ := line_from_points A B (by euclid_finish)
  obtain ⟨AC, hA', hC⟩ := line_from_points A C (by euclid_finish)
  obtain ⟨f, hf⟩ := proposition_9' A B C AB AC (by euclid_finish)
  obtain ⟨L, hL⟩ := line_from_points B f (by euclid_finish)
  use L
  intro P
  apply Iff.intro
  · intro hh
    sorry
  · intro hh
    sorry

theorem triangle_angleSum_c : ∀(A B C : Point) , triangle A B C → ∠A:B:C +∠B:C:A + ∠C:A:B = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points C A as CA
  euclid_apply extend_point BC B C as D
  euclid_apply Book_triangle_angleSum A B C D AB BC CA
  euclid_finish

theorem unique_perpLine : ∀ (A : Point) (L : Line),
  ¬(A.onLine L)
  → ∃! (M : Line),
    A.onLine M
    ∧ perpLine L M
    :=
by
  intro A L hAL
  obtain ⟨A', hA'⟩ := exists_foot A L (by euclid_finish)
  obtain ⟨M, hM⟩ := line_from_points A A' (by euclid_finish)
  use M
  apply And.intro
  · euclid_finish
  · intro M' hM'
    suffices ∀ x : Point, x.onLine M' → x.onLine M by
      euclid_finish
    intro x hx
    -- M' is a line through A perpendicular to L. Let X be its intersection with L.
    obtain ⟨X, hX⟩ := hM'.2
    -- This setup implies that X is the foot of the perpendicular from A to L.
    have h_foot_X: foot A X L := by
      euclid_finish
    -- We already have A' as the foot of the perpendicular from A to L.
    -- The foot is unique, so X must be the same point as A'.
    have h_X_is_A': X = A' := by
      by_cases h_eq : X = A'
      · assumption
      · have h_neq : X ≠ A' := h_eq
        -- A is not on L, but X and A' are on L. So A, X, A' form a triangle.
        have h_tri : triangle A X A' := by euclid_finish
        -- Since A' is the foot of the perpendicular from A to L, and X is on L, angle A:A':X is a right angle.
        have h_ang_A' : ∠ A:A':X = ∟ := by
          have h := hA'.2.2 X
          have c : X.onLine L ∧ A' ≠ X := by euclid_finish
          specialize h c
          euclid_finish
        -- Similarly, since X is the foot of the perpendicular from A to L, and A' is on L, angle A:X:A' is a right angle.
        have h_ang_X : ∠ A:X:A' = ∟ := by
          have h := h_foot_X.2.2 A'
          have c : A'.onLine L ∧ X ≠ A' := by euclid_finish
          specialize h c
          euclid_finish
        -- The sum of angles in triangle A-X-A' is 180 degrees.
        have h_sum: ∠ A:X:A' + ∠ A:A':X + ∠ X:A:A' = ∟ + ∟ := by
          euclid_apply triangle_angleSum_c A X A'
          euclid_finish
        -- This implies angle X:A:A' must be zero.
        have h_ang_A_is_zero : ∠ X:A:A' = 0 := by
          linarith
        -- A zero angle between segments from a common point implies the three points are collinear.
        have h_not_tri : ¬ triangle A X A' := by euclid_finish
        contradiction
    -- Now we know that X and A' are the same point.
    -- We are given that M' passes through A (hM'.1) and X, so it must pass through A'.
    have h_A_on_M' : A.onLine M' := by euclid_finish
    have h_A'_on_M' : A'.onLine M' := by
      have h_X_on_M' : X.onLine M' := by euclid_finish
      have h_eq : X = A' := h_X_is_A'
      euclid_finish
    -- By hypothesis, x is on line M' (hx). Since A and A' are also on M', they are all collinear.
    have h_coll : coll x A A' := by
      euclid_finish
    -- The line M was constructed as the line passing through A and A'.
    -- Any point collinear with A and A' must lie on M.
    euclid_finish

example (A B : Prop) : (A ↔ B) ↔ ((A → B) ∧ (B → A)) :=
  iff_iff_implies_and_implies A B

example (A B : Prop) : (A ↔ B) ↔ ((A → B) ∧ (B → A)) :=
  iff_iff_implies_and_implies A B

theorem exists_inCentre : ∀ (A B C: Point), triangle A B C → ∃ (I : Point), inCentre I A B C := by
  intro A B C hABC
  obtain ⟨L1, hL1⟩ := exists_angleBisection A B C (by euclid_finish)
  simp [iff_iff_implies_and_implies] at hL1
  obtain ⟨L2, hL2⟩ := exists_angleBisection A C B (by euclid_finish)
  simp [iff_iff_implies_and_implies] at hL2
  have : L1.intersectsLine L2 := by sorry
  obtain ⟨I, hI⟩ := intersection_lines L1 L2 this
  use I
  simp only [inCentre]
  apply And.intro
  · sorry
  apply And.intro
  · specialize hL2 I
    have : I ≠ C := sorry
    have := hL2.1 (by euclid_finish)
    have : ∠ I:C:A = ∠ A:C:I := by euclid_finish
    euclid_finish
  · specialize hL1 I
    have : I ≠ B := sorry
    have := hL1.1 (by euclid_finish)
    have : ∠ A:B:I = ∠ I:B:A := by euclid_finish
    euclid_finish

end LeanGeo
