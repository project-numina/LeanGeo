import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem similar_19 : ∀ (H I J K : Point) (HI IJ HJ IK : Line),
  formTriangle H I K HI IK HJ ∧
  formTriangle I J K IJ HJ IK ∧
  between H K J ∧
  ∠ H:K:I = ∟ ∧ ∠ I:K:J = ∟ ∧
  ∠ H:I:J = ∟ →
  SimilarTriangles I J K H I K :=
by
  euclid_intros
  -- euclid_assert ∠ I:K:J = ∠ H:K:I
  have : ∠ K:H:I + ∠ H:I:K = ∟ := by
    euclid_apply triangle_angles_sum K I H
    euclid_finish
  have : ∠ I:H:J + ∠ H:J:I = ∟ := by
    euclid_apply triangle_angles_sum I J H
    euclid_finish
  -- euclid_assert ∠ H:I:K = ∠ H:J:I'
  euclid_apply similar_AA I J K H I K
  euclid_finish
