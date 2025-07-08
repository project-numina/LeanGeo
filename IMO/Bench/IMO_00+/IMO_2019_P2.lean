import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--In triangle $ABC$, point $A_1$ lies on side $BC$ and point $B_1$ lies on side $AC$. Let $P$ and $Q$ be points on segments $AA_1$ and $BB_1$, respectively, such that $PQ$ is parallel to $AB$. Let $P_1$ be a point on line $PB_1$, such that $B_1$ lies strictly between $P$ and $P_1$, and $\angle PP_1C=\angle BAC$. Similarly, let $Q_1$ be the point on line $QA_1$, such that $A_1$ lies strictly between $Q$ and $Q_1$, and $\angle CQ_1Q=\angle CBA$. Prove that points $P,Q,P_1$, and $Q_1$ are concyclic.
theorem IMO_2019_P2 :
  ∀ (A B C A1 B1 P Q P1 Q1 : Point)
    (BC AC AA1 BB1 PQ AB PB1 QA1 : Line),
    distinctPointsOnLine B C BC ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine A A1 AA1 ∧
    distinctPointsOnLine B B1 BB1 ∧
    between B A1 C ∧
    between A B1 C ∧
    between A P A1 ∧
    between B Q B1 ∧
    distinctPointsOnLine P Q PQ ∧
    distinctPointsOnLine A B AB ∧
    ¬ AB.intersectsLine PQ ∧
    distinctPointsOnLine P B1 PB1 ∧
    P1.onLine PB1 ∧
    between P B1 P1 ∧
    distinctPointsOnLine Q A1 QA1 ∧
    Q1.onLine QA1 ∧
    between Q A1 Q1 ∧
    ∠ P:P1:C = ∠ B:A:C ∧
    ∠ C:Q1:Q = ∠ C:B:A →
    cyclic P Q P1 Q1 := by
  sorry