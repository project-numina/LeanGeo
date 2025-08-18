import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Problem 2.28 (JMO 2012/1). Given a triangle $A B C$, let $P$ and $Q$ be points on segments $\overline{A B}$ and $\overline{A C}$, respectively, such that $A P=A Q$. Let $S$ and $R$ be distinct points on segment $\overline{B C}$ such that $S$ lies between $B$ and $R, \angle B P S=\angle P R S$, and $\angle C Q R=\angle Q S R$. Prove that $P, Q, R, S$ are concyclic.
theorem JMO_2012_1 :
  ∀ (A B C P Q R S : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    between A P B ∧ between A Q C ∧ |(A─P)| = |(A─Q)| ∧
    between B S C ∧ between B R C ∧ between B S R ∧ S ≠ R ∧
    ∠ B:P:S = ∠ P:R:S ∧ ∠ C:Q:R = ∠ Q:S:R →
    cyclic P Q R S := by sorry