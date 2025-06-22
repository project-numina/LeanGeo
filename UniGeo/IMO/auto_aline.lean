import SystemE
import UniGeo.Relations
import UniGeo.Abbre


open SystemE

theorem imo_shortlist_p2021_g4 : ∀ (A B C D : Point) (L₁ L₂ : Line) (Γ : Circle),
True → True
:= by
  sorry


theorem p2022_IMO_Shortlist_G1 :
∀ (A B C D E T P Q R S : Point)
  (AB BC CD DE EA CT DT : Line),
(formPentagon A B C D E AB BC CD DE EA)
∧ (|(B─C)| = |(D─E)|)
∧ (|(T─B)| = |(T─D)|)
∧ (|(T─C)| = |(T─E)|)
∧ (∠ A:B:T = ∠ T:E:A)
∧ twoLinesIntersectAtPoint AB CD P
∧ twoLinesIntersectAtPoint AB CT Q
∧ between P B A
∧ between B A Q
∧ twoLinesIntersectAtPoint AE CD R
∧ twoLinesIntersectAtPoint AE DT S
∧ between R E A
∧ between E A S
→ cyclic P S Q R
:= by
sorry

theorem p2018_IMO_Shortlist_G2 :
∀ (A B C M P X Y : Point) (AB BC CA PB PC PA : Line),
  formTriangle A B C AB BC CA
  ∧ |(A─B)| = |(A─C)|
  ∧ midpoint B M C
  ∧ (|(P─B)| < |(P─C)|)
  ∧ ¬(∃ Q : Point, twoLinesIntersectAtPoint PA BC Q)
  ∧ threePointsOnLine P B X PB
  ∧ between P B X
  ∧ threePointsOnLine P C Y PC
  ∧ between P C Y
  ∧ ∠P:X:M = ∠P:Y:M
→ cyclic A P X Y := by
sorry

theorem p2018_IMO_Shortlist_G6 :
∀ (A B C D X : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (|(A─B)| * |(C─D)|) = (|(B─C)| * |(D─A)|) ∧
  (∠ X:A:B = ∠ X:C:D) ∧
  (∠ X:B:C = ∠ X:D:A)
  → ∠ B:X:A + ∠ D:X:C = ∟ + ∟
:= by
sorry


theorem p2021_IMO_Shortlist_G2 :
  ∀ (A B C D I X Y T Z : Point) (AB BC CD DA : Line) (Γ Ω : Circle),
  I.isCentre Γ ∧
  formQuadrilateral A B C D AB BC CD DA ∧
  tangentLine AB Γ ∧ tangentLine BC Γ ∧
  tangentLine CD Γ ∧ tangentLine DA Γ ∧
  circumCircle Ω A I C ∧
  X.onLine AB ∧ X.onCircle Ω ∧
  Z.onLine BC ∧ Z.onCircle Ω ∧
  Y.onLine DA ∧ Y.onCircle Ω ∧
  T.onLine CD ∧ T.onCircle Ω
  → |(A─D)| + |(D─T)| + |(T─X)| + |(X─A)| = |(C─D)| + |(D─Y)| + |(Y─Z)| + |(Z─C)| :=
by sorry


theorem p2019_IMO_Shortlist_G4 :
  ∀ (A B C P A1 B1 C1 A2 B2 C2 : Point)
    (AB BC CA AP BP CP : Line)
    (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    distinctPointsOnLine A P AP ∧
    twoLinesIntersectAtPoint AP BC A1 ∧
    distinctPointsOnLine B P BP ∧
    twoLinesIntersectAtPoint BP CA B1 ∧
    distinctPointsOnLine C P CP ∧
    twoLinesIntersectAtPoint CP AB C1 ∧
    midpoint P A1 A2 ∧
    midpoint P B1 B2 ∧
    midpoint P C1 C2 ∧
    circumCircle Ω A B C
  → ¬(A2.insideCircle Ω ∧ B2.insideCircle Ω ∧ C2.insideCircle Ω) :=
by
  sorry

 theorem imo_shortlist_p2019_g3 :
∀ (A B C A1 B1 P Q P1 Q1 : Point)
  (AB BC CA AA1 BB1 PB1 QA1 PQ : Line),
  formTriangle A B C AB BC CA ∧
  A1.onLine BC ∧
  B1.onLine CA ∧
  P.onLine AA1 ∧
  Q.onLine BB1 ∧
  P1.onLine PB1 ∧
  Q1.onLine QA1 ∧
  (∀ X : Point, ¬ twoLinesIntersectAtPoint PQ AB X) ∧
  between P B1 P1 ∧
  between Q A1 Q1 ∧
  (∠P:P1:C = ∠B:A:C) ∧
  (∠C:Q1:Q = ∠C:B:A)
  → cyclic P Q P1 Q1 := by
sorry
 theorem IMO_p2017_Shortlist_G3 :
∀ (A B C O P Q H R M : Point)
  (AB BC CA OA altB altC AM : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  distinctPointsOnLine B H altB ∧
  perpLine altB CA ∧
  distinctPointsOnLine C H altC ∧
  perpLine altC AB ∧
  twoLinesIntersectAtPoint altB altC H ∧
  twoLinesIntersectAtPoint OA altB P ∧
  twoLinesIntersectAtPoint OA altC Q ∧
  circumCentre R P Q H ∧
  midpoint B M C ∧
  distinctPointsOnLine A M AM
  → R.onLine AM := by
sorry

theorem p2020_IMO_Shortlist_G8 :
∀
(A B C I P M Q N X Y : Point)
(AB BC CA PM QN YB YC L : Line)
(Γ ωB ωC : Circle),
formTriangle A B C AB BC CA ∧
circumCircle Γ A B C ∧
B.onCircle ωB ∧
I.onCircle ωB ∧
C.onCircle ωC ∧
I.onCircle ωC ∧
P.onCircle ωB ∧
P.onCircle Γ ∧
M.onCircle ωB ∧
M.onLine AB ∧
distinctPointsOnLine M B AB ∧
Q.onCircle ωC ∧
Q.onCircle Γ ∧
N.onCircle ωC ∧
N.onLine AC ∧
distinctPointsOnLine N C AC ∧
distinctPointsOnLine P M PM ∧
distinctPointsOnLine Q N QN ∧
twoLinesIntersectAtPoint PM QN X ∧
distinctPointsOnLine Y B YB ∧
tangentLine YB ωB ∧
distinctPointsOnLine Y C YC ∧
tangentLine YC ωC
→ threePointsOnLine A X Y L
:= by
  sorry

theorem p2018_IMO_Shortlist_G7 :
∀ (A B C O P O_A O_B O_C X Y Z : Point)
  (AB BC CA OP l_A l_B l_C XY YZ ZX : Line)
  (Ω ω' : Circle),
  formTriangle A B C AB BC CA
  ∧ circumCentre O A B C
  ∧ circumCircle Ω A B C
  ∧ P.onCircle Ω
  ∧ A ≠ P
  ∧ B ≠ P
  ∧ C ≠ P
  ∧ circumCentre O_A A O P
  ∧ circumCentre O_B B O P
  ∧ circumCentre O_C C O P
  ∧ O_A.onLine l_A
  ∧ perpLine l_A BC
  ∧ O_B.onLine l_B
  ∧ perpLine l_B CA
  ∧ O_C.onLine l_C
  ∧ perpLine l_C AB
  ∧ twoLinesIntersectAtPoint l_A l_B X
  ∧ twoLinesIntersectAtPoint l_B l_C Y
  ∧ twoLinesIntersectAtPoint l_C l_A Z
  ∧ formTriangle X Y Z XY YZ ZX
  ∧ circumCircle ω' X Y Z
  → tangentLine OP ω' := by
sorry

theorem imo_p2017_shortlist_g1 :
  ∀ (A B C D E X : Point) (AB BC CD DE EA AC BD L : Line),
  formPentagon A B C D E AB BC CD DE EA ∧
  |(A─B)| = |(B─C)| ∧
  |(B─C)| = |(C─D)| ∧
  ∠ E:A:B = ∠ B:C:D ∧
  ∠ E:D:C = ∠ C:B:A ∧
  E.onLine L ∧
  perpLine L BC
  → twoLinesIntersectAtPoint AC BD X ∧
    twoLinesIntersectAtPoint BD L X
:= by sorry


theorem p2018_IMO_Shortlist_G1 :
  ∀ (A B C D E F G : Point)
    (AB BC CA BD CE BDperp CEperp DE FG : Line)
    (Γ : Circle),
  (formTriangle A B C AB BC CA
   ∧ between A D B
   ∧ between A E C
   ∧ |(A─D)| = |(A─E)|
   ∧ circumCircle Γ A B C
   ∧ perpBisector B D BDperp
   ∧ perpBisector C E CEperp
   ∧ F.onLine BDperp
   ∧ F.onCircle Γ
   ∧ G.onLine CEperp
   ∧ G.onCircle Γ)
  → (¬(∃ P : Point, twoLinesIntersectAtPoint DE FG P) ∨ (DE = FG))
:= by
sorry


theorem p2019_IMO_Shortlist_G6 :
∀ (A B C I D E F P Q : Point) (AB BC CA EF : Line) (ω Γ : Circle),
  formTriangle A B C AB BC CA ∧
  I.isCentre ω ∧
  tangentAtPoint BC ω D ∧
  tangentAtPoint CA ω E ∧
  tangentAtPoint AB ω F ∧
  D.onLine BC ∧
  E.onLine CA ∧
  F.onLine AB ∧
  circumCircle Γ A B C ∧
  distinctPointsOnLine E F EF ∧
  P.onLine EF ∧
  P.onCircle Γ ∧
  Q.onLine EF ∧
  Q.onCircle Γ ∧
  between E F P
  → ∠D:P:A + ∠A:Q:D = ∠Q:I:P
:= by
  sorry


theorem imo_p2022_shortlist_g2 :
∀ (A B C F P D E X Y : Point) (AB BC CA AF PD PE : Line),
  formTriangle A B C AB BC CA ∧
  threePointsOnLine B C F BC ∧
  threePointsOnLine A F P AF ∧
  perpLine AF BC ∧
  between A P F ∧
  P.onLine PD ∧
  ¬(PD.intersectsLine AC) ∧
  twoLinesIntersectAtPoint PD BC D ∧
  P.onLine PE ∧
  ¬(PE.intersectsLine AB) ∧
  twoLinesIntersectAtPoint PE BC E ∧
  cyclic A B D X ∧
  X ≠ A ∧
  |(D─A)| = |(D─X)| ∧
  cyclic A C E Y ∧
  Y ≠ A ∧
  |(E─A)| = |(E─Y)|
  → cyclic B C X Y
:= by
  sorry


theorem p2019_IMO_Shortlist_G2 :
∀ (A B C D E F M N P Q : Point)
  (AB BC CA AD BE CF DE DF MN : Line)
  (ω_B ω_C : Circle),
  formTriangle A B C AB BC CA ∧
  perpLine AD BC ∧ twoLinesIntersectAtPoint AD BC D ∧
  perpLine BE CA ∧ twoLinesIntersectAtPoint BE CA E ∧
  perpLine CF AB ∧ twoLinesIntersectAtPoint CF AB F ∧
  M.onLine DF ∧ M.onCircle ω_B ∧ tangentAtPoint DF ω_B M ∧
  N.onLine DE ∧ N.onCircle ω_C ∧ tangentAtPoint DE ω_C N ∧
  distinctPointsOnLine M N MN ∧
  P.onLine MN ∧ P.onCircle ω_B ∧ ¬(P = M) ∧
  Q.onLine MN ∧ Q.onCircle ω_C ∧ ¬(Q = N)
  → |(M─P)| = |(N─Q)| :=
by
  sorry


theorem p2022_IMOShortlist_G6 :
∀ (A B C H : Point)
  (AB BC CA AH : Line),
  formTriangle A B C AB BC CA ∧
  H.onLine BC ∧
  perpLine AH BC
  →
  ∃ (X : Point),
    ∀ (P E F Q : Point)
      (PB PC AC AB EF PQ : Line),
      (∠ P:B:E = ∠ E:B:C ∧ E.onLine AC) ∧
      (∠ P:C:F = ∠ F:C:B ∧ F.onLine AB) ∧
      twoLinesIntersectAtPoint EF AH Q ∧
      distinctPointsOnLine P B PB ∧
      distinctPointsOnLine P C PC ∧
      distinctPointsOnLine P Q PQ
      →
      X.onLine PQ
:= by
  sorry

theorem p2022_IMO_Shortlist_G3 :
∀ (A B C D Q P M N : Point)
   (AB BC CD DA AC BD QAB : Line)
   (O1 O2 O3 O4 : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  threePointsOnLine Q A B QAB ∧
  P.onLine QAB ∧
  between Q A B ∧
  between A B P ∧
  A.onCircle O1 ∧ D.onCircle O1 ∧ Q.onCircle O1 ∧
  tangentLine AC O1 ∧
  B.onCircle O2 ∧ C.onCircle O2 ∧ P.onCircle O2 ∧
  tangentLine BD O2 ∧
  midpoint B M C ∧
  midpoint A N D ∧
  A.onCircle O3 ∧ N.onCircle O3 ∧ Q.onCircle O3 ∧
  B.onCircle O4 ∧ M.onCircle O4 ∧ P.onCircle O4 ∧
  tangentAtPoint T1 O3 A ∧
  tangentAtPoint T2 O4 B
  → ∃ X : Point, X.onLine CD ∧ X.onLine T1 ∧ X.onLine T2 := by
sorry

 theorem p2023_ISL_G8 :
∀ (A B C A1 B1 C1 A2 B2 C2 : Point)
  (BC1 CB1 CA1 AC1 AB1 BA1 : Line)
  (ΩA ΩB ΩC : Circle),
  (|(A─B)| = |(B─C)|) ∧ (|(B─C)| = |(C─A)|)
  ∧ (|(B─A1)| = |(A1─C)|) ∧ (|(C─B1)| = |(B1─A)|) ∧ (|(A─C1)| = |(C1─B)|)
  ∧ (∠ B:A1:C + ∠ C:B1:A + ∠ A:C1:B = 480)
  ∧ distinctPointsOnLine B C1 BC1 ∧ distinctPointsOnLine C B1 CB1 ∧ twoLinesIntersectAtPoint BC1 CB1 A2
  ∧ distinctPointsOnLine C A1 CA1 ∧ distinctPointsOnLine A C1 AC1 ∧ twoLinesIntersectAtPoint CA1 AC1 B2
  ∧ distinctPointsOnLine A B1 AB1 ∧ distinctPointsOnLine B A1 BA1 ∧ twoLinesIntersectAtPoint AB1 BA1 C2
  ∧ (|(A1─B1)| ≠ |(B1─C1)|) ∧ (|(B1─C1)| ≠ |(C1─A1)|) ∧ (|(C1─A1)| ≠ |(A1─B1)|)
  ∧ circumCircle ΩA A A1 A2
  ∧ circumCircle ΩB B B1 B2
  ∧ circumCircle ΩC C C1 C2
  →
  ∃ (P Q : Point),
    P ≠ Q
    ∧ P.onCircle ΩA ∧ P.onCircle ΩB ∧ P.onCircle ΩC
    ∧ Q.onCircle ΩA ∧ Q.onCircle ΩB ∧ Q.onCircle ΩC
:= by
  sorry

theorem p2021_IMO_Shortlist_G5 :
∀ (A B C D O B1 D1 O_B O_D : Point)
  (AB BC CD DA AC BD1 DB1 OBOD : Line)
  (Ω ΓB ΓD : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  (|(A─B)| ≠ |(B─C)|) ∧
  (|(B─C)| ≠ |(C─D)|) ∧
  (|(C─D)| ≠ |(D─A)|) ∧
  (|(A─B)| ≠ |(C─D)|) ∧
  (|(B─C)| ≠ |(D─A)|) ∧
  (|(A─B)| ≠ |(D─A)|) ∧
  O.isCentre Ω ∧
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
  B1.onLine AC ∧ ∠A:B:B1 = ∠B1:B:C ∧
  D1.onLine AC ∧ ∠A:D:D1 = ∠D1:D:C ∧
  O_B.isCentre ΓB ∧ B.onCircle ΓB ∧ tangentAtPoint AC ΓB D1 ∧
  O_D.isCentre ΓD ∧ D.onCircle ΓD ∧ tangentAtPoint AC ΓD B1 ∧
  distinctPointsOnLine B D1 BD1 ∧
  distinctPointsOnLine D B1 DB1 ∧
  distinctPointsOnLine O_B O_D OBOD ∧
  ¬(∃ P : Point, twoLinesIntersectAtPoint BD1 DB1 P)
  → O.onLine OBOD
:= by
  sorry

 theorem ISL_p2023_G3 :
∀ (A B C D P M X : Point) (AB BC CD DA PM : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  ∠B:A:D < ∠A:D:C ∧
  ∠A:D:B = ∠C:P:D ∧
  ∠A:D:P = ∠P:C:B
  → ∃ (X : Point), twoLinesIntersectAtPoint DA PM X ∧ X.onLine BC
:= by
sorry

 theorem p2023_ISL_G1 :
∀ (A B C D E M O MBE : Point)
  (AB BC CD DE EA AO : Line),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine E A EA ∧
  distinctPointsOnLine A O AO ∧
  (∠ A:B:C = ∟) ∧
  (∠ A:E:D = ∟) ∧
  midpoint C M D ∧
  circumCentre M A B E ∧
  circumCentre O A C D ∧
  midpoint B MBE E
→ MBE.onLine AO := by
sorry

theorem p2017_IMO_Shortlist_G5 :
∀ (A B C C_1 B_1 A_1 D E X : Point)
  (AC_1 A_1C BB_1 DE L : Line)
  (ω ω2 : Circle),
  distinctPointsOnLine A C_1 AC_1 ∧
  distinctPointsOnLine A_1 C A_1C ∧
  twoLinesIntersectAtPoint AC_1 A_1C D ∧
  circumCircle ω A B C ∧
  circumCircle ω2 A_1 B C_1 ∧
  E.onCircle ω ∧
  E.onCircle ω2 ∧
  (E ≠ B) ∧
  distinctPointsOnLine B B_1 BB_1 ∧
  distinctPointsOnLine D E DE ∧
  perpBisector A A_1 L ∧
  perpBisector B B_1 L ∧
  perpBisector C C_1 L ∧
  |(A─B)|=|(B─C)|
→ twoLinesIntersectAtPoint BB_1 DE X ∧ X.onCircle ω
:= by
sorry

 theorem p2023_ISL_G5 :
∀
(A B C D E X Y P O : Point)
(AB BC CA BD CE CO BO AO : Line)
(ω G1 G2 : Circle),
  formTriangle A B C AB BC CA
∧ O.isCentre ω
∧ circumCircle ω A B C
∧ distinctPointsOnLine B D BD
∧ D.onCircle ω
∧ perpLine BD AC
∧ distinctPointsOnLine C E CE
∧ E.onCircle ω
∧ perpLine CE AB
∧ distinctPointsOnLine C O CO
∧ twoLinesIntersectAtPoint CO AB X
∧ distinctPointsOnLine B O BO
∧ twoLinesIntersectAtPoint BO AC Y
∧ distinctPointsOnLine A O AO
∧ circumCircle G1 B X D
∧ circumCircle G2 C Y E
∧ P.onCircle G1
∧ P.onCircle G2
→ P.onLine AO := by
sorry

theorem p2017_IMO_Shortlist_G2 :
∀
(R S T J A K : Point)
(l LAJ LKT : Line)
(Ω Γ : Circle),
R ≠ S ∧
R.onCircle Ω ∧
S.onCircle Ω ∧
tangentAtPoint l Ω R ∧
midpoint R S T ∧
J.onCircle Ω ∧
circumCircle Γ J S T ∧
(∃ (X Y : Point), X.onLine l ∧ X.onCircle Γ ∧ Y.onLine l ∧ Y.onCircle Γ ∧ X ≠ Y) ∧
A.onLine l ∧
A.onCircle Γ ∧
distinctPointsOnLine A J LAJ ∧
K.onLine LAJ ∧
K.onCircle Ω ∧
K ≠ A ∧
K ≠ J ∧
distinctPointsOnLine K T LKT
→ tangentLine LKT Γ
:= by
sorry

theorem imo_p2020_shortlist_g7 :
∀ (A B C P D E F X Y Z Q : Point)
  (AB BC CA L_A L_B L_C lAD lBE lCF XY YZ ZX : Line)
  (circleABC circleADP circleBEP circleCFP ω : Circle),
  (formTriangle A B C AB BC CA)
  ∧ (circumCircle circleABC A B C)
  ∧ (P.onCircle circleABC)
  ∧ (perpBisector P D L_A)
  ∧ (perpBisector P E L_B)
  ∧ (perpBisector P F L_C)
  ∧ (perpBisector A D lAD)
  ∧ (perpBisector B E lBE)
  ∧ (perpBisector C F lCF)
  ∧ (twoLinesIntersectAtPoint lAD lBE X)
  ∧ (twoLinesIntersectAtPoint lBE lCF Y)
  ∧ (twoLinesIntersectAtPoint lCF lAD Z)
  ∧ (formTriangle X Y Z XY YZ ZX)
  ∧ (circumCircle ω X Y Z)
  ∧ (circumCircle circleADP A D P)
  ∧ (circumCircle circleBEP B E P)
  ∧ (circumCircle circleCFP C F P)
  → ∃ (T : Point),
      T.onCircle circleADP
      ∧ T.onCircle circleBEP
      ∧ T.onCircle circleCFP
      ∧ T.onCircle ω
:= by
  sorry
 theorem p2023_ISL_G2 :
  ∀ (A B C P S D Q E : Point)
    (AB BC CA AC BP SP AE BE CQ DQ : Line)
    (ω : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle ω A B C ∧
  P.onLine AC ∧
  |(B─C)| = |(C─P)| ∧
  threePointsOnLine B P D BP ∧
  D.onCircle ω ∧
  S.onLine AB ∧
  distinctPointsOnLine P S SP ∧
  perpLine SP AB ∧
  threePointsOnLine S P Q SP ∧
  between S P Q ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine C Q CQ ∧
  perpLine AE CQ ∧
  distinctPointsOnLine B E BE ∧
  distinctPointsOnLine D Q DQ ∧
  perpLine BE DQ
  → E.onCircle ω := by
sorry

theorem p2018_IMO_Shortlist_G4 :
∀
(A B C T A1 B1 C1 A2 B2 C2 : Point)
(AB BC CA A1T B1T C1T AA2 BB2 CC2 : Line)
(Ω : Circle),
formTriangle A B C AB BC CA ∧
T.sameSide A BC ∧ T.sameSide B CA ∧ T.sameSide C AB ∧
perpBisector T A1 BC ∧
perpBisector T B1 CA ∧
perpBisector T C1 AB ∧
formTriangle A1 B1 C1 A1B1 B1C1 C1A1 ∧
circumCircle Ω A1 B1 C1 ∧
threePointsOnLine A1 T A2 A1T ∧ A2.onCircle Ω ∧
threePointsOnLine B1 T B2 B1T ∧ B2.onCircle Ω ∧
threePointsOnLine C1 T C2 C1T ∧ C2.onCircle Ω ∧
distinctPointsOnLine A A2 AA2 ∧
distinctPointsOnLine B B2 BB2 ∧
distinctPointsOnLine C C2 CC2
→ ∃ (P : Point),
  twoLinesIntersectAtPoint AA2 BB2 P ∧
  P.onLine CC2 ∧
  P.onCircle Ω
:= by
sorry


theorem p2023_ISL_G4 :
∀
(A B C S D E L P X : Point)
(AB BC CA BS AD BE DL TLine : Line)
(Ω ω : Circle),
  formTriangle A B C AB BC CA
∧ |(A─B)| < |(A─C)|
∧ (∠B:A:C < ∟ ∧ ∠C:B:A < ∟ ∧ ∠A:C:B < ∟)
∧ circumCircle Ω A B C
∧ (S.onCircle Ω ∧ distinctPointsOnLine B S BS)
∧ (perpLine AD BC ∧ distinctPointsOnLine A D AD ∧ twoLinesIntersectAtPoint AD BS D)
∧ (E.onCircle Ω ∧ E.onLine AD ∧ E ≠ A)
∧ distinctPointsOnLine B E BE
∧ (distinctPointsOnLine D L DL ∧ ¬(DL.intersectsLine BC) ∧ twoLinesIntersectAtPoint DL BE L)
∧ circumCircle ω B D L
∧ (P.onCircle ω ∧ P.onCircle Ω ∧ P ≠ B)
∧ tangentAtPoint TLine ω P
∧ twoLinesIntersectAtPoint TLine BS X
→ ∠B:A:X = ∠X:A:C
:= by
  sorry

theorem IMO_p2019_Sh_G1 :
∀ (A B C D E F G T : Point)
  (AB BC CA AT L1 L2 : Line)
  (Γ cBDF cCEG : Circle),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B C BC ∧
  A.onCircle Γ ∧
  D.onCircle Γ ∧
  E.onCircle Γ ∧
  F.onCircle Γ ∧
  G.onCircle Γ ∧
  D.onLine AB ∧
  E.onLine AC ∧
  F.onLine BC ∧
  G.onLine BC ∧
  between B F G ∧
  B.onCircle cBDF ∧
  D.onCircle cBDF ∧
  F.onCircle cBDF ∧
  C.onCircle cCEG ∧
  E.onCircle cCEG ∧
  G.onCircle cCEG ∧
  tangentAtPoint L1 cBDF F ∧
  tangentAtPoint L2 cCEG G ∧
  twoLinesIntersectAtPoint L1 L2 T ∧
  distinctPointsOnLine A T AT ∧
  A ≠ T
→ ¬(∃ X : Point, twoLinesIntersectAtPoint AT BC X) :=
by sorry

theorem p2020_IMO_Shortlist_G3 :
∀ (A B C D E F K L : Point) (AB BC CD DA BD AE AF : Line) (ω₁ ω₂ : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  (∠ A:B:C > ∟) ∧
  (∠ C:D:A > ∟) ∧
  (∠ D:A:B = ∠ B:C:D) ∧
  perpBisector A E BC ∧
  perpBisector A F CD ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine A F AF ∧
  twoLinesIntersectAtPoint AE BD K ∧
  twoLinesIntersectAtPoint AF BD L ∧
  circumCircle ω₁ B E K ∧
  circumCircle ω₂ D F L
  → ∀ (P Q : Point),
      (P.onCircle ω₁ ∧ P.onCircle ω₂ ∧ Q.onCircle ω₁ ∧ Q.onCircle ω₂)
      → P = Q
:= by
  sorry


theorem imo_p2021_shortlist_g7 :
∀
(A B C D E F X O₁ O₂ : Point)
(AB BC CA AD DC EX XD DE EF O₁O₂ : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| > |(A─C)| ∧
  ∠D:A:B = ∠C:A:D ∧
  formTriangle A D C AD DC CA ∧
  circumCentre O₁ A D C ∧
  formTriangle E X D EX XD DE ∧
  circumCentre O₂ E X D ∧
  between A E C ∧
  ∠A:D:E = ∠B:C:D ∧
  between A F B ∧
  ∠F:D:A = ∠D:B:C ∧
  X.onLine CA ∧
  |(C─X)| = |(B─X)| ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine O₁ O₂ O₁O₂
→ ∃ (P : Point), P.onLine BC ∧ P.onLine EF ∧ P.onLine O₁O₂
:= by
  sorry


theorem p2018_IMO_Shortlist_G5 :
∀
(A B C I D E F P Q R T1 T2 : Point)
(AB BC CA AI BI CI ℓ x y z PQ QR RP : Line)
(Ω Θ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Ω A B C ∧

  distinctPointsOnLine A I AI ∧
  distinctPointsOnLine B I BI ∧
  distinctPointsOnLine C I CI ∧

  D.onLine AI ∧ D.onLine ℓ ∧
  E.onLine BI ∧ E.onLine ℓ ∧
  F.onLine CI ∧ F.onLine ℓ ∧

  perpBisector A D x ∧
  perpBisector B E y ∧
  perpBisector C F z ∧

  twoLinesIntersectAtPoint x y P ∧
  twoLinesIntersectAtPoint y z Q ∧
  twoLinesIntersectAtPoint z x R ∧

  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine Q R QR ∧
  distinctPointsOnLine R P RP ∧
  formTriangle P Q R PQ QR RP ∧

  circumCircle Θ P Q R
→
  ∀ (T1 T2 : Point),
    (T1.onCircle Ω ∧ T1.onCircle Θ ∧ T2.onCircle Ω ∧ T2.onCircle Θ)
    → (T1 = T2)
:= by
sorry


theorem p2022_IMO_Shortlist_G5 :
∀ (A B C X₁ Y₁ Z₁ X₂ Y₂ Z₂ A₁ B₁ C₁ A₂ B₂ C₂ : Point)
  (ℓ₁ ℓ₂ BC CA AB X₁Line Y₁Line Z₁Line X₂Line Y₂Line Z₂Line : Line)
  (Ω₁ Ω₂ : Circle),
  formTriangle A B C BC CA AB ∧
  ¬(∃ P : Point, twoLinesIntersectAtPoint ℓ₁ ℓ₂ P) ∧
  twoLinesIntersectAtPoint ℓ₁ BC X₁ ∧
  twoLinesIntersectAtPoint ℓ₁ CA Y₁ ∧
  twoLinesIntersectAtPoint ℓ₁ AB Z₁ ∧
  twoLinesIntersectAtPoint ℓ₂ BC X₂ ∧
  twoLinesIntersectAtPoint ℓ₂ CA Y₂ ∧
  twoLinesIntersectAtPoint ℓ₂ AB Z₂ ∧
  (X₁.onLine X₁Line ∧ perpLine X₁Line BC) ∧
  (Y₁.onLine Y₁Line ∧ perpLine Y₁Line CA) ∧
  (Z₁.onLine Z₁Line ∧ perpLine Z₁Line AB) ∧
  twoLinesIntersectAtPoint X₁Line Y₁Line A₁ ∧
  twoLinesIntersectAtPoint Y₁Line Z₁Line B₁ ∧
  twoLinesIntersectAtPoint Z₁Line X₁Line C₁ ∧
  circumCircle Ω₁ A₁ B₁ C₁ ∧
  (X₂.onLine X₂Line ∧ perpLine X₂Line BC) ∧
  (Y₂.onLine Y₂Line ∧ perpLine Y₂Line CA) ∧
  (Z₂.onLine Z₂Line ∧ perpLine Z₂Line AB) ∧
  twoLinesIntersectAtPoint X₂Line Y₂Line A₂ ∧
  twoLinesIntersectAtPoint Y₂Line Z₂Line B₂ ∧
  twoLinesIntersectAtPoint Z₂Line X₂Line C₂ ∧
  circumCircle Ω₂ A₂ B₂ C₂
  → (∃ T : Point, T.onCircle Ω₁ ∧ T.onCircle Ω₂) ∧ ¬( Ω₁.intersectsCircle Ω₂)
:= by
sorry


theorem imo_shortlist_p2022_g8 :
∀ (A A' B B' C C' X Y : Point)
  (O inc₁ inc₂ : Circle)
  (AB A'B' BC B'C' AC A'C' XB BY YB' B'X : Line),
  (
    A.onCircle O ∧ A'.onCircle O ∧ B.onCircle O ∧ B'.onCircle O ∧ C.onCircle O ∧ C'.onCircle O
  )
  ∧
  (
    distinctPointsOnLine A C AC ∧ tangentLine AC inc₁
  )
  ∧
  (
    distinctPointsOnLine A' C' A'C' ∧ tangentLine A'C' inc₂
  )
  ∧
  (
    twoLinesIntersectAtPoint AB A'B' X ∧ twoLinesIntersectAtPoint BC B'C' Y
  )
  ∧
  (
    formQuadrilateral X B Y B' XB BY YB' B'X
  )
  → ∃ (I : Circle),
    tangentLine XB I ∧
    tangentLine BY I ∧
    tangentLine YB' I ∧
    tangentLine B'X I
:= by
  sorry


theorem p2019_IMO_Shortlist_G7 :
∀
(A B C I D E F R P Q S : Point)
(AB BC CA EF DR AR DI PQ AI L PC CE EP PB BF : Line)
(ω Ω1 Ω2 : Circle),
  formTriangle A B C AB BC CA
∧ |(A─B)| ≠ |(A─C)|
∧ I.isCentre ω
∧ tangentAtPoint BC ω D
∧ tangentAtPoint CA ω E
∧ tangentAtPoint AB ω F
∧ D.onLine BC
∧ E.onLine CA
∧ F.onLine AB
∧ D.onCircle ω
∧ E.onCircle ω
∧ F.onCircle ω
∧ distinctPointsOnLine E F EF
∧ distinctPointsOnLine D R DR
∧ R.onCircle ω
∧ perpLine EF DR
∧ distinctPointsOnLine A R AR
∧ P.onLine AR
∧ P.onCircle ω
∧ formTriangle P C E PC CE EP
∧ formTriangle P B F PB BF FP
∧ circumCircle Ω1 P C E
∧ circumCircle Ω2 P B F
∧ Q.onCircle Ω1
∧ Q.onCircle Ω2
∧ distinctPointsOnLine D I DI
∧ distinctPointsOnLine P Q PQ
∧ distinctPointsOnLine A I AI
→
  twoLinesIntersectAtPoint DI PQ S
∧ distinctPointsOnLine A S L
∧ perpLine AI L
:= by
  sorry


theorem imo_shortlist_p2022_g7 :
∀ (A B C A' B' C' H O P Q R M : Point)
  (AB BC CA A'B' B'C' C'A' AA' BB' CC' PQ QR RP OH : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  formTriangle A' B' C' A'B' B'C' C'A' ∧
  -- Express “A,B,C and A’,B’,C’ share the same orthocenter H” as a single premise:
  -- (In a fully expanded formalization, one would specify perpendiculars & concurrency,
  --  but here we treat it as a given statement.)
  -- sameOrthocenter A B C A' B' C' H
  -- For brevity in this framework, we denote it directly:
  -- "TheyHaveSameOrthocenter A B C A' B' C' H"
  -- in lieu of a built-in predicate.
  -- -------------------------------------------------
  -- Here we simply encode it textually:
  -- -------------------------------------------------
  -- “Triangles ABC, A'B'C' have the same orthocenter H”
  -- -------------------------------------------------
  -- We do not introduce new definitions, so treat it as a premise:
  -- -------------------------------------------------
  (True) ∧  -- placeholder for the shared orthocenter premise
  circumCircle Ω A B C ∧
  O.isCentre Ω ∧
  A'.onCircle Ω ∧ B'.onCircle Ω ∧ C'.onCircle Ω ∧
  distinctPointsOnLine A A' AA' ∧
  distinctPointsOnLine B B' BB' ∧
  distinctPointsOnLine C C' CC' ∧
  twoLinesIntersectAtPoint BB' CC' P ∧
  twoLinesIntersectAtPoint CC' AA' Q ∧
  twoLinesIntersectAtPoint AA' BB' R ∧
  distinctPointsOnLine O H OH ∧
  circumCentre M P Q R
→ M.onLine OH
:= by
  sorry


theorem p2023_ISL_G7 :
∀ (A B C H : Point)
  (AB BC CA BH CH : Line)
  (B₁ C₁ : Point) (ℓ_a : Line)
  (B₂ C₂ : Point) (ℓ_b : Line)
  (B₃ C₃ : Point) (ℓ_c : Line)
  (P Q R : Point)
  (O H_T : Point)
  (L : Line),
  -- 1)  ABC is a scalene acute triangle with orthocenter H
  formTriangle A B C AB BC CA ∧

  -- 2)  Define reflections:
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine C H CH ∧
  perpBisector B B₁ CH ∧
  perpBisector C C₁ BH ∧
  distinctPointsOnLine B₁ C₁ ℓ_a ∧

  -- (Similarly for ℓ_b and ℓ_c):
  perpBisector B B₂ CH ∧
  perpBisector C C₂ BH ∧
  distinctPointsOnLine B₂ C₂ ℓ_b ∧

  perpBisector B B₃ CH ∧
  perpBisector C C₃ BH ∧
  distinctPointsOnLine B₃ C₃ ℓ_c ∧

  -- 3)  Lines ℓ_a, ℓ_b, ℓ_c form triangle 𝓣 with vertices P,Q,R
  formTriangle P Q R ℓ_a ℓ_b ℓ_c ∧

  -- 4)  O is the circumcenter of triangle 𝓣
  circumCentre O P Q R

  -- 5)  H_T is the orthocenter of triangle 𝓣 (not formally defined here)
  --     (placeholder for the usual "altitudes concur at H_T")
  --     ...

  -- Conclusion: H, O, and H_T are collinear
  --
  -- Expressed here as three distinct points on some line L:
  → threePointsOnLine O H_T H L
:= by
  sorry

theorem p2020_IMO_Shortlist_G1 :
∀ (A B C D P Q E F : Point) (AB BC CA L L2 : Line) (Γ1 Γ2 : Circle),
  formTriangle A B C AB BC CA
  ∧ ( |(B─C)| = |(C─A)| )
  ∧ between A D B
  ∧ between B P C
  ∧ between C Q A
  ∧ ( ∠ D:P:B = ∟ )
  ∧ ( ∠ D:Q:A = ∟ )
  ∧ perpBisector P Q L
  ∧ E.onLine L
  ∧ E.onLine CA
  ∧ between C E Q
  ∧ circumCircle Γ1 A B C
  ∧ circumCircle Γ2 C P Q
  ∧ F.onCircle Γ1
  ∧ F.onCircle Γ2
  ∧ (F ≠ C)
  ∧ threePointsOnLine P E F L2
  → ( ∠ A:C:B = ∟ ) := by
sorry


theorem imo_p2021_shortlist_g1 :
∀
(A B C D P Q R X : Point)
(AB BC CD DA PD PC AQ BR : Line)
(Ω Θ : Circle),
formQuadrilateral A B C D AB BC CD DA
∧ ¬(∃ M : Point, twoLinesIntersectAtPoint AB DC M)
∧ ¬(∃ N : Point, twoLinesIntersectAtPoint BC DA N)
∧ |(A─C)| = |(B─C)|
∧ distinctPointsOnLine A B AB
∧ P.onLine AB
∧ between A B P
∧ distinctPointsOnLine C D CD
∧ distinctPointsOnLine P D PD
∧ circumCircle Ω A C D
∧ Q.onLine PD
∧ Q.onCircle Ω
∧ between P Q D
∧ distinctPointsOnLine P C PC
∧ circumCircle Θ A P Q
∧ R.onLine PC
∧ R.onCircle Θ
∧ between P R C
∧ distinctPointsOnLine A Q AQ
∧ distinctPointsOnLine B R BR
→ ∃ (X : Point),
  X.onLine CD
  ∧ X.onLine AQ
  ∧ X.onLine BR
:= by
sorry
