import SystemE
import UniGeo.Theorem


open SystemE

--theorem exists_centre : ∀ (O: Circle), ∃ (C : Point), C.isCentre O := by
--  sorry

theorem chord_inside : ∀ (O: Circle) (A B C: Point), A.onCircle O ∧ B.onCircle O ∧ between A C B → C.insideCircle O := by
  euclid_intros
  euclid_finish

theorem two_perpAngle_eqPoint: ∀ (O A B: Point), (∠O:A:B = ∟) ∧ (∠O:B:A = ∟) → A = B := by
  sorry

theorem chord_bisector : ∀ (O A B: Point) (C: Circle) (AB L: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ perpLine AB L
  → O.onLine L →  perpBisector A B L := by
  euclid_intros
  euclid_apply intersection_lines AB L as F
  have h1 : |(A─F)| = |(F─B)| := by
    by_cases triangle A B O
    . euclid_assert isoTriangle O A B
      euclid_assert coll A B F
      euclid_assert perpLineatPoint AB L F
      simp at *
      have h2 : A ≠ F := by
        by_contra
        euclid_assert ∠B:A:O = ∟
        euclid_apply eqside_eqangle O A B
        euclid_assert ∠A:B:O = ∟
        euclid_apply two_perpAngle_eqPoint O A B
        euclid_finish
      have h3: B ≠ F := by
        by_contra
        euclid_assert ∠A:B:O = ∟
        euclid_apply eqside_eqangle O A B
        euclid_assert ∠B:A:O = ∟
        euclid_apply two_perpAngle_eqPoint O A B
        euclid_finish
      euclid_assert ∠A:F:O = ∟
      euclid_apply isoTriangle_threeLine_concidence O A B F
      euclid_finish
    · euclid_assert between A O B
      euclid_assert O = F
      euclid_finish

  euclid_apply (perpBisector_equiv A B L).mpr
  euclid_finish
