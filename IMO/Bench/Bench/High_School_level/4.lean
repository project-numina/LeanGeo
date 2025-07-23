import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo


theorem Numina_Geometry_617 :
  ∀ (a b c d e f : Point) (BD EF : Line),
    Triangle a b c ∧
    Coll a d c ∧
    Coll b e c ∧
    Coll d f c ∧
    distinctPointsOnLine b d BD ∧
    distinctPointsOnLine e f EF ∧
    ∠ a:b:d = ∠ d:b:c ∧
    ∠ b:d:e = ∠ e:d:c ∧
    ∠ d:e:f = ∠ f:e:c ∧
    ¬ (BD.intersectsLine EF)
    → ∠ a:b:c = ∠ b:a:c + ∠ b:a:c := by
    euclid_intros
    euclid_apply line_from_points d e as DE
    euclid_assert b.opposingSides f DE
    euclid_apply parallel_imp_eq_alternateAngles BD EF DE d e b f
    have h1 : between b e c:= by
      euclid_apply angle_bisector_between d b c e
      euclid_finish
    have h2 : between a d c := by
      euclid_apply angle_bisector_between b a c d
      euclid_finish
    euclid_apply triangle_exterior_angle_sum b e d c
    have h3 : ∠a:b:c = ∠a:b:d + ∠c:b:d := by
      euclid_apply between_angleSum b a d c
      euclid_finish
    have h4 : ∠b:d:c = ∠d:b:a + ∠b:a:d := by
      euclid_apply triangle_exterior_angle_sum a d b c
      euclid_finish
    have h5 : ∠b:a:c = ∠b:a:d := by
      euclid_apply coll_angles_eq a d c b
      euclid_finish
    rw [h3, h5]
    have h6 : ∠c:b:d = ∠e:d:b := by
      euclid_apply line_from_points b c as BC
      have h7: ∠c:b:d = ∠c:e:f := by
        euclid_apply parallel_imp_eq_alternateExteriorAngles f e d b c EF BD BC
        euclid_finish
      euclid_finish
    have h8: 2 * ∠e:d:b = ∠b:d:c := by
      have h11: ∠b:d:c = ∠e:d:b + ∠e:d:c := by
        euclid_apply between_angleSum d b e c
        euclid_finish
      rw [h11]
      euclid_finish
    have h9: ∠c:b:d = ∠d:a:b := by
      have h10: ∠c:b:d = (∠c:b:d + ∠d:a:b) / 2 := by
        calc
          _ = ∠e:d:b := by rw[h6]
          _ = ∠ b:d:c / 2 := by
            rw[← h8]
            linarith
          _ = (∠d:b:a + ∠b:a:d)/2 := by rw [h4]
          _ = _ := by
            euclid_finish
      linarith
    rw[h9]
    euclid_finish
