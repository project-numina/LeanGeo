import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Triangle $BCF$ has a right angle at $B$. Let $A$ be the point on line $CF$ such that $FA=FB$ and $F$ lies between $A$ and $C$. Point $D$ is chosen so that $DA=DC$ and $AC$ is the bisector of $\angle{DAB}$. Point $E$ is chosen so that $EA=ED$ and $AD$ is the bisector of $\angle{EAC}$. Let $M$ be the midpoint of $CF$. Let $X$ be the point such that $AMXE$ is a parallelogram. Prove that $BD,FX$ and $ME$ are concurrent.
theorem IMO_2016_P1 :
  ∀ (B C F A D E M X : Point)
    (BC CF FB AM MX XE EA BD FX ME : Line),
    formTriangle B C F BC CF FB ∧
    ∠ C:B:F = ∟ ∧
    A.onLine CF ∧ between A F C ∧ |(F─A)| = |(F─B)| ∧
    |(D─A)| = |(D─C)| ∧ ∠ D:A:C = ∠ C:A:B ∧
    |(E─A)| = |(E─D)| ∧ ∠ E:A:D = ∠ D:A:C ∧
    between C M F ∧ |(C─M)| = |(M─F)| ∧
    parallelogram A M X E AM MX XE EA →
    concurrent BD FX ME := by
  sorry