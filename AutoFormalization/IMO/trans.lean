import SystemE
import UniGeo.Relations
import UniGeo.Abbre

theorem problem_MP33 :
  ∀ (A B C D : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ D.onLine CA
  ∧ |(A─B)| = |(A─C)|
  ∧ |(A─D)| = (|(B─D)| + |(B─C)|)
  ∧ ∠ B:D:C = 60
  → ∠ B:A:C = 20
:= by
  sorry

theorem problem_MP71 : ∀ (A B C M N E F : Point),
  |(A─M)|=|(A─N)| ∧
  |(B─F)|=|(C─E)| ∧
  |(F─N)|=|(E─M)|
  → |(A─B)|=|(A─C)| := by
  sorry

theorem problem_MP73 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    D.onLine AB ∧
    E.onLine CA ∧
    |(A─D)| = |(A─E)| ∧
    ∠ D:C:B = ∠ E:B:C
    → |(A─B)| = |(A─C)| :=
by sorry

theorem problem_MP6 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  between A D C ∧
  between A E B ∧
  |(A─D)| = |(A─E)| ∧
  |(B─D)| = |(C─E)|
  → |(A─B)| = |(A─C)| := by
sorry

theorem problem_MP3 :
  ∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  insideTriangle D A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  ∠A:D:B = ∠A:D:C
  → ∠B:A:D = ∠D:A:C := by
  sorry

theorem problem_MP75 :
  ∀ (A B C D O : Point) (AB BC CD DA AC BD : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    twoLinesIntersectAtPoint AC BD O ∧
    (|(A─B)| + |(A─C)| = |(D─B)| + |(D─C)|) ∧
    (|(O─B)| > |(O─C)|)
  → (|(O─A)| > |(O─D)|) := by
  sorry

theorem problem_MP74 :
  ∀ (A B C P : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| > |(A─C)|) ∧
  insideTriangle P A B C AB BC CA ∧
  (∠B:A:P < ∠C:A:P)
  → (|(A─B)| - |(A─C)| > |(P─B)| - |(P─C)|)
:= by
  sorry

theorem problem_MP20 :
  ∀ (A B C D E F : Point) (AB BC CA DE DF : Line),
    formTriangle A B C AB BC CA ∧
    midpoint B D C ∧
    E.onLine CA ∧ distinctPointsOnLine D E DE ∧ perpLine DE CA ∧
    F.onLine AB ∧ distinctPointsOnLine D F DF ∧ perpLine DF AB ∧
    |(B─E)| = |(C─F)|
  → |(A─B)| = |(A─C)| :=
by
  sorry

theorem problem_MP76 :
  ∀ (A B C D E : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  D.onLine BC ∧
  E.onLine AD ∧
  ∠A:D:B = 60 ∧
  |(D─E)| = |(D─C)|
  → |(B─E)| = |(A─B)| := by
  sorry

theorem problem_MP93 :
∀ (A B C D M E F : Point) (AB BC CA AD EM : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧
  ∠B:A:D = ∠D:A:C ∧
  midpoint B M C ∧
  E.onLine CA ∧ |(A─E)|=|(A─B)| ∧
  distinctPointsOnLine E M EM ∧
  twoLinesIntersectAtPoint EM AD F
  → |(B─F)|=|(B─D)| := by
sorry

theorem problem_MP58 :
  ∀ (A B C D E F G : Point) (AB BC CA AD EF : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  E.onLine AB ∧
  F.onLine AC ∧
  |(B─E)| = |(C─F)| ∧
  twoLinesIntersectAtPoint AD EF G ∧
  midpoint E G F
  → |(A─B)| = |(A─C)| :=
by sorry

theorem problem_MP12 :
∀ (A B C D : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(A─C)|)
  ∧ (∠B:A:C = 20)
  ∧ D.onLine CA
  ∧ (∠A:B:D = ∠D:B:C)
  → |(A─D)| = (|(B─D)| + |(B─C)|)
:= by
  sorry

theorem problem_MP10 : ∀
(A B C D : Point)
(AB BC CA : Line),
formTriangle A B C AB BC CA ∧
|(A─B)| = |(A─C)| ∧
midpoint A D C ∧
(∠A:B:D = 30)
→ (|(A─B)|=|(B─C)| ∧ |(B─C)|=|(C─A)|) := by
sorry

theorem problem_HP97 :
  ∀ (A B C O I : Point) (AB BC CA OI AI : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  inCentre I A B C ∧
  distinctPointsOnLine O I OI ∧
  distinctPointsOnLine A I AI ∧
  perpLine OI AI
  → (|(A─B)| + |(A─C)|) = (|(B─C)| + |(B─C)|) := by
sorry

theorem problem_imo_2012_p5 :
  ∀ (A B C D X K L M : Point) (AB BC CA CD AX BX AL BK : Line),
  formTriangle A B C AB BC CA ∧
  ∠ B:C:A = ∟ ∧
  D.onLine AB ∧
  distinctPointsOnLine C D CD ∧
  perpLine AB CD ∧
  between C X D ∧
  K.onLine AX ∧
  between A K X ∧
  |(B─K)| = |(B─C)| ∧
  L.onLine BX ∧
  between B L X ∧
  |(A─L)| = |(A─C)| ∧
  twoLinesIntersectAtPoint AL BK M
  → |(M─K)| = |(M─L)| :=
by sorry

theorem problem_MP52 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(A─C)| ∧
    ∠ B:A:C = 80 ∧
    D.onLine BC ∧
    ∠ B:A:D = 50 ∧
    E.onLine CA
  → |(A─B)| = |(A─C)| :=
by
  sorry

theorem problem_MP9 :
  ∀ (A B C : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ (∠ B:A:C = ∠ A:C:B + ∠ A:C:B + ∠ A:C:B)
  ∧ (|(B─C)| = |(A─B)| + |(A─B)|)
  → ∠ B:A:C = ∟
:= by
  sorry

theorem problem_MP64 : ∀
(A B C D E F : Point)
(BC BD AC AE BF CE DF : Line),
  A.sameSide D BC ∧
  ∠ B:A:C = ∟ ∧
  ∠ B:D:C = ∟ ∧
  E.onLine BD ∧
  F.onLine AC ∧
  perpLine AE BF ∧
  perpLine DF CE
  → |(A─F)| * |(A─C)| = |(D─E)| * |(D─B)| := by
sorry

theorem problem_MP23 :
  ∀ (A B C D : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  (∠C:A:B + ∠A:B:C + ∠B:C:A = ∟ + ∟) ∧
  ∠C:A:B = 100 ∧
  ∠A:C:B = 30 ∧
  threePointsOnLine A C D AD ∧
  between A C D ∧
  |(C─D)| = |(A─B)|
  → ∠C:D:B = 20
:= by
  sorry

theorem problem_HP13 :
  ∀ (A B C D E F G : Point) (AB BC CA DE BE CD : Line) (O P : Circle),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧
  E.onLine AC ∧
  distinctPointsOnLine D E DE ∧
  ¬(DE.intersectsLine BC) ∧
  distinctPointsOnLine B E BE ∧
  distinctPointsOnLine C D CD ∧
  twoLinesIntersectAtPoint BE CD F ∧
  circumCircle O B D F ∧
  circumCircle P C E F ∧
  G.onCircle O ∧
  G.onCircle P
  → ∠B:A:F = ∠C:A:G
:= by
  sorry

theorem problem_MP35 : ∀
  (A B C D : Point)
  (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(B─C)| = |(C─D)| ∧
  ∠A:D:B = 30 ∧
  ∠A:B:D = ∠D:B:C + 60
  → ∠C:A:D = 30 := by
sorry

theorem problem_HP71 :
  ∀ (A B C D E F H O M N : Point)
    (AB BC CA AD BE CF ED FD MN OH: Line),
    formTriangle A B C AB BC CA ∧
    twoLinesIntersectAtPoint BC AD D ∧ perpLine BC AD ∧
    twoLinesIntersectAtPoint CA BE E ∧ perpLine CA BE ∧
    twoLinesIntersectAtPoint AB CF F ∧ perpLine AB CF ∧
    twoLinesIntersectAtPoint AD BE H ∧ H.onLine CF ∧
    circumCentre O A B C ∧
    twoLinesIntersectAtPoint ED AB M ∧
    twoLinesIntersectAtPoint FD AC N ∧
    distinctPointsOnLine O H OH ∧
    distinctPointsOnLine M N MN
  → perpLine OH MN
:= by
  sorry

theorem problem_MP26 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠ A:C:B = ∟ ∧
    ∠ A:B:C = 30 ∧
    D.onLine BC ∧
    E.onLine AC ∧
    ∠ B:A:D = 40 ∧
    ∠ A:B:E = 20
    → ∠ A:D:E = 30
:= by
  sorry

theorem problem_MP67 :
  ∀ (A B C D E O : Point) (AB BC CA BE CD : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧
  E.onLine AC ∧
  (|(B─D)| = |(C─E)|) ∧
  twoLinesIntersectAtPoint BE CD O ∧
  (|(O─D)| = |(O─E)|)
  → (|(A─B)| = |(A─C)|) := by
  sorry

theorem problem_MP97 :
∀ (A B C D E F G : Point) (AB BC CD DA AC AD EF : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (∠B:A:D = ∠A:D:C)
  ∧ (E.onLine BC)
  ∧ (between B E C)
  ∧ (|(B─E)| = |(A─B)|)
  ∧ (|(C─E)| = |(C─D)|)
  ∧ (¬(EF.intersectsLine AB))
  ∧ (twoLinesIntersectAtPoint EF AC G)
  ∧ (twoLinesIntersectAtPoint EF AD F)
  → (|(E─G)| = |(G─F)|)
:= by
  sorry

theorem problem_HP95 :
  ∀ (P A B C D E : Point) (PA PB PCD : Line) (O : Circle),
  tangentAtPoint PA O A ∧
  tangentAtPoint PB O B ∧
  P.onLine PA ∧ A.onLine PA ∧
  P.onLine PB ∧ B.onLine PB ∧
  P.onLine PCD ∧ C.onLine PCD ∧ D.onLine PCD ∧
  A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O ∧
  midpoint A E B
  → ∠ A : C : D = ∠ B : C : E :=
by
  sorry

theorem problem_09G4 :
  ∀ (A B C D E F G H : Point)
    (AB BC CD DA AC BD EF : Line)
    (Ω : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint AC BD E ∧
  twoLinesIntersectAtPoint DA BC F ∧
  midpoint A G B ∧
  midpoint C H D ∧
  distinctPointsOnLine E F EF ∧
  circumCircle Ω E G H
  → tangentLine EF Ω := by
  sorry

theorem problem_HP60 :
  ∀ (A B C D E F O P Q R : Point) (AB BC CA DE BE CD : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧
  E.onLine AC ∧
  distinctPointsOnLine D E DE ∧
  ¬(DE.intersectsLine BC) ∧
  distinctPointsOnLine B E BE ∧
  distinctPointsOnLine C D CD ∧
  twoLinesIntersectAtPoint BE CD F ∧
  circumCentre O A D F ∧
  circumCentre P A E F ∧
  circumCentre Q B D F ∧
  circumCentre R C E F
  → cyclic O P Q R := by
  sorry

theorem problem_MP19 :
∀ (A B C D E F P : Point)
  (AB BC CD DA BD AE CF AC : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine A E AE ∧
  twoLinesIntersectAtPoint AE BD E ∧
  perpLine AE BD ∧
  distinctPointsOnLine C F CF ∧
  twoLinesIntersectAtPoint CF BD F ∧
  perpLine CF BD ∧
  distinctPointsOnLine A C AC ∧
  midpoint A P C
→ |(P─E)| = |(P─F)| :=
by sorry

theorem problem_MP18 : ∀
  (A B C D E : Point)
  (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧
  D.onLine BC ∧
  E.onLine BC ∧
  between B C D ∧
  between C B E ∧
  (∠A:B:E = 2 * ∠A:C:D) ∧
  perpLine AD CA
  → |(C─D)| = 2 * |(A─B)| := by
  sorry

theorem problem_MP79 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  ∠ B:A:C = 80 ∧
  D.onLine BC ∧
  ∠ B:A:D = 50 ∧
  E.onLine CA ∧
  ∠ A:B:E = 40
  → ∠ A:D:E = 30 :=
by
  sorry

theorem problem_MP39 :
  ∀ (A B C D E H : Point) (AB BC CA CH BD : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(A─C)| ∧
    H.onLine AB ∧
    distinctPointsOnLine C H CH ∧
    perpLine AB CH ∧
    D.onLine CH ∧
    distinctPointsOnLine B D BD ∧
    twoLinesIntersectAtPoint BD CA E ∧
    |(A─B)| = |(B─E)| ∧
    |(A─D)| = |(A─E)|
  → ∠A:B:C = 80 :=
by sorry

theorem problem_MP28 : ∀
  (A B C D : Point)
  (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠ B:A:C = 60 ∧
  ∠ A:C:B = 20 ∧
  D.onLine BC ∧
  ∠ B:A:D = 20
  → |(A─B)| + |(A─D)| = |(D─C)|
:= by
  sorry

theorem problem_HP90 :
∀ (A B C D E F M N : Point) (AB BC CA AD EF DF MN : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  distinctPointsOnLine A D AD ∧
  D.onCircle O ∧
  ∠B:A:D = ∠D:A:C ∧
  midpoint B E C ∧
  distinctPointsOnLine E F EF ∧
  perpLine EF AD ∧
  distinctPointsOnLine D F DF ∧
  distinctPointsOnLine M N MN ∧
  perpLine MN DF ∧
  M.onLine AB ∧
  N.onLine AC
  → |(F─M)| = |(F─N)| :=
by
  sorry

theorem problem_MP41 :
∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C = ∟/2 ∧
  ∠A:C:B = ∟/6 ∧
  D.onLine BC ∧
  ∠C:A:D = ∟/2
→ |(C─D)| = |(B─D)| + |(B─D)| :=
by
  sorry

theorem problem_MP22 :
∀ (A B C D E : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(B─C)|)
  ∧ (|(B─C)| = |(C─A)|)
  ∧ between A D B
  ∧ between C B E
  ∧ (|(A─D)| = |(B─E)|)
  → (|(C─D)| = |(E─D)|) := by
  sorry

theorem problem_14G6 :
∀ (A B C E1 F1 M1 K1 S1 T1 E2 F2 M2 K2 S2 T2 : Point)
  (AB BC CA L1_1 L1_2 L2_1 L2_2 : Line),
  (formTriangle A B C AB BC CA)
  ∧ (E1.onLine AC)
  ∧ (F1.onLine AB)
  ∧ (midpoint E1 M1 F1)
  ∧ (perpBisector E1 F1 L1_1)
  ∧ (twoLinesIntersectAtPoint L1_1 BC K1)
  ∧ (perpBisector M1 K1 L2_1)
  ∧ (twoLinesIntersectAtPoint L2_1 AC S1)
  ∧ (twoLinesIntersectAtPoint L2_1 AB T1)
  ∧ (cyclic K1 S1 A T1)
  ∧ (E2.onLine AC)
  ∧ (F2.onLine AB)
  ∧ (midpoint E2 M2 F2)
  ∧ (perpBisector E2 F2 L1_2)
  ∧ (twoLinesIntersectAtPoint L1_2 BC K2)
  ∧ (perpBisector M2 K2 L2_2)
  ∧ (twoLinesIntersectAtPoint L2_2 AC S2)
  ∧ (twoLinesIntersectAtPoint L2_2 AB T2)
  ∧ (cyclic K2 S2 A T2)
  → ( |(E1 ─ E2)| * |(A ─ C)| ) = ( |(F1 ─ F2)| * |(A ─ B)| )
:= by
  sorry

theorem problem_MP70 :
  ∀ (A B C D O : Point) (AB BC CD DA AC BD : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint AC BD O ∧
  ( |(A─B)| + |(A─C)| = |(D─B)| + |(D─C)| ) ∧
  ( |(O─B)| > |(O─C)| )
  → ( |(O─A)| > |(O─D)| ) :=
by
  sorry

theorem problem_MP72 :
∀ (A B C D E F G : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine AB ∧
  E.onLine AC ∧
  (|(B─D)| = |(C─E)|) ∧
  F.onLine BC ∧
  G.onLine BC ∧
  (|(B─F)| = |(C─G)|) ∧
  (∠B:F:C = ∠B:G:C)
  → (|(A─B)| = |(A─C)|) := by
sorry

theorem problem_HP61 :
∀ (A B C I D E F M N G H : Point)
  (AB BC CA ED FD AI AH : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  I.isCentre Ω ∧
  tangentAtPoint BC Ω D ∧ D.onLine BC ∧ D.onCircle Ω ∧
  tangentAtPoint AB Ω E ∧ E.onLine AB ∧ E.onCircle Ω ∧
  tangentAtPoint AC Ω F ∧ F.onLine AC ∧ F.onCircle Ω ∧
  distinctPointsOnLine A I AI ∧
  twoLinesIntersectAtPoint ED AI M ∧
  twoLinesIntersectAtPoint FD AI N ∧
  midpoint B G C ∧
  H.onLine BC ∧
  distinctPointsOnLine A H AH ∧
  perpLine AH BC
  → cyclic G N H M :=
by sorry

theorem problem_17G1 :
  ∀ (A B C D E : Point) (AB BC CD DE EA : Line),
    formPentagon A B C D E AB BC CD DE EA ∧
    |(A─B)| = |(B─C)| ∧
    |(B─C)| = |(C─D)| ∧
    ∠E:A:B = ∠B:C:D
    → ∠E:D:C = ∠E:A:B + ∠B:C:D
    := by
  sorry

theorem problem_06G4 :
∀ (A B C D J K L : Point)
  (AB BC CA BD CD KL AJ : Line)
  (incircle : Circle),
  formTriangle A B C AB BC CA ∧
  |(A─B)| < |(B─C)| ∧
  D.onLine CA ∧
  |(B─D)| = |(B─A)| ∧
  formTriangle B C D BC CD BD ∧
  inCentre J B C D ∧
  inCircle incircle AB BC CA ∧
  K.onLine AB ∧ K.onCircle incircle ∧
  L.onLine AC ∧ L.onCircle incircle ∧
  distinctPointsOnLine K L KL ∧
  distinctPointsOnLine A J AJ
  → ∃ (X : Point),
    X.onLine KL ∧
    X.onLine AJ ∧
    midpoint A X J
:= by
  sorry

theorem problem_MP77 :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| = |(A─C)| ∧
    ∠ A:C:D = 30 ∧
    ∠ D:B:C = 30
  → ∠ B:A:C = ∠ C:A:D + ∠ C:A:D :=
by
  sorry

theorem problem_MP47 :
  ∀ (A B C D E : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (|(A─B)| = |(B─C)|) ∧ (|(B─C)| = |(C─D)|) ∧ (|(C─D)| = |(D─A)|) ∧
  (∠ A:B:C = 78) ∧
  insideQuadrilateral E A B C D AB BC CD DA ∧
  (∠ E:A:D = 21) ∧
  (∠ E:D:A = 9)
  → (|(B─C)| = |(C─E)|) ∧ (|(C─E)| = |(E─B)|)
:= by
  sorry

theorem problem_imo_22_p4 : ∀
(A B C D E T P Q R S : Point)
(AB BC CD DE EA CT DT : Line),
formPentagon A B C D E AB BC CD DE EA ∧
|(B─C)| = |(D─E)| ∧
|(T─B)| = |(T─D)| ∧
|(T─C)| = |(T─E)| ∧
∠ A:B:T = ∠ T:E:A ∧
twoLinesIntersectAtPoint AB CD P ∧
twoLinesIntersectAtPoint AB CT Q ∧
between P B A ∧
between B A Q ∧
twoLinesIntersectAtPoint AE CD R ∧
twoLinesIntersectAtPoint AE DT S ∧
between R E A ∧
between E A S
→ cyclic P S Q R := by
sorry

theorem problem_HP23 :
∀ (A B C O D E F L M N : Point) (AB BC CA DE OF : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  between A D B ∧
  between A E C ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine O F OF ∧
  twoLinesIntersectAtPoint OF DE F ∧
  perpLine OF DE ∧
  midpoint D L E ∧
  midpoint B M E ∧
  midpoint C N D
  → cyclic F L M N
:= by
  sorry

theorem problem_MP46 :
  ∀ (A B C D : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    (∠A:B:C < (2*∟)/3) ∧
    (∠A:C:B = ∟/3) ∧
    insideTriangle D A B C AB BC CA ∧
    (|(D─B)| = |(D─C)|) ∧
    (∠A:B:C + ∠D:B:C = (2*∟)/3)
  → (∠C:A:D = ∟/3)
:= by
  sorry

theorem problem_imo_2004_p5 :
  ∀ (A B C D P : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    (∠ A:B:D ≠ ∠ D:B:C) ∧
    (∠ C:D:B ≠ ∠ B:D:A) ∧
    insideQuadrilateral P A B C D AB BC CD DA ∧
    (∠ P:B:C = ∠ D:B:A) ∧
    (∠ P:D:C = ∠ B:D:A)
    → ((cyclic A B C D → (|(A─P)| = |(C─P)|)) ∧ (|(A─P)| = |(C─P)| → cyclic A B C D)) :=
by
  sorry


theorem HP7 :
  ∀ (A B C M F G I : Point) (AB BC CA CF FG GC : Line),
    formTriangle A B C AB BC CA ∧
    formTriangle C F G CF FG GC ∧
    |(A─C)| = |(B─C)| ∧
    midpoint A M B ∧
    inCentre I A B C ∧
    inCentre I C F G ∧
    M.onLine FG
    → |(A─M)| * |(A─M)| = |(F─M)| * |(G─M)| :=
by sorry

theorem problem_18G1 :
∀ (A B C D E F G T : Point) (AB BC CA AT L1 L2 : Line) (Γ ω1 ω2 : Circle),
  (formTriangle A B C AB BC CA)
  ∧ A.onCircle Γ
  ∧ D.onCircle Γ ∧ D.onLine AB
  ∧ E.onCircle Γ ∧ E.onLine CA
  ∧ F.onCircle Γ ∧ F.onLine BC
  ∧ G.onCircle Γ ∧ G.onLine BC
  ∧ between B F G
  ∧ circumCircle ω1 B D F
  ∧ circumCircle ω2 C E G
  ∧ tangentAtPoint L1 ω1 F
  ∧ tangentAtPoint L2 ω2 G
  ∧ twoLinesIntersectAtPoint L1 L2 T
  ∧ distinctPointsOnLine A T AT
→ ¬(AT.intersectsLine BC)
:= by
  sorry

theorem problem_MP87 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠A:B:C = ∟ ∧
    midpoint B D C ∧
    E.onLine CA ∧
    (|(A─E)| = 2 * |(C─E)|)
    → ∠A:D:B = ∠C:D:E
:= by
  sorry

theorem problem_HP55 :
  ∀ (A B C D E F O : Point)
    (lAB lCB lCD lAD lOC lEB lFB : Line)
    (circ : Circle),
  O.isCentre circ ∧
  A.onCircle circ ∧
  B.onCircle circ ∧
  midpoint A O B ∧
  distinctPointsOnLine C B lCB ∧
  tangentAtPoint lCB circ B ∧
  D.onCircle circ ∧
  distinctPointsOnLine C D lCD ∧
  F.onCircle circ ∧
  F.onLine lCD ∧
  twoLinesIntersectAtPoint lAD lOC E ∧
  distinctPointsOnLine A D lAD ∧
  distinctPointsOnLine O C lOC ∧
  distinctPointsOnLine E B lEB ∧
  distinctPointsOnLine F B lFB
  → perpLine lEB lFB := by
sorry

theorem problem_MP81 :
  ∀ (A B C D E F : Point) (AB BC CA AD : Line),
    formTriangle A B C AB BC CA ∧
    ∠B:A:C = ∟ ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B C BC ∧
    twoLinesIntersectAtPoint AD BC D ∧
    perpLine AD BC ∧
    E.onLine AB ∧
    F.onLine CA ∧
    ∠E:D:F = ∟
  → (|(B─E)| * |(A─C)|) = (|(A─B)| * |(A─F)|) :=
by sorry

theorem problem_MP80 :
  ∀ (A B C M N D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  M.onLine AB ∧
  N.onLine AC ∧
  D.onLine BC ∧
  E.onLine BC ∧
  |(A─M)| = |(A─N)| ∧
  |(B─D)| = |(C─E)| ∧
  (|(B─D)| < (|(B─C)|)/2) ∧
  (∠B:M:D = ∠C:N:E)
  → (|(A─B)| = |(A─C)|) :=
by
  sorry

theorem problem_MP57 :
  ∀ (A B C D E P : Point) (AB BC CD DA BP CE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine CD) ∧
  ¬(BC.intersectsLine AD) ∧
  midpoint A E D ∧
  distinctPointsOnLine B P BP ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint BP CE P ∧
  perpLine BP CE
  → |(A─P)| = |(A─B)| := by
  sorry

theorem HP88 :
  ∀ (A B C D E F M O : Point) (AB BC CA AD EF : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC ∧
  midpoint B M C ∧
  twoLinesIntersectAtPoint EF AB E ∧
  twoLinesIntersectAtPoint EF AC F ∧
  M.onLine EF ∧
  |(A─E)| = |(A─F)| ∧
  circumCentre O A E F
  → |(O─M)| = |(O─D)| :=
by sorry

theorem problem_HP34 :
∀ (A B C D E F : Point)
  (AB BC CD DA AC BD : Line)
  (O : Circle),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D A DA ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  E.onLine BD ∧
  ∠ E:C:B = ∠ A:C:D ∧
  circumCircle O A B D ∧
  A.onLine AC ∧
  C.onLine AC ∧
  F.onLine AC ∧
  F.onCircle O
→ ∠ B:F:E = ∠ A:F:D
:= by
  sorry

theorem HP39 :
  ∀ (A B C P Q D E F G M N L : Point)
    (AB BC CA DE FG PQ BN CM AL : Line)
    (circP circQ : Circle),
  formTriangle A B C AB BC CA ∧
  P.isCentre circP ∧
  Q.isCentre circQ ∧
  tangentAtPoint CB circP D ∧
  tangentAtPoint CA circP E ∧
  tangentAtPoint BC circQ F ∧
  tangentAtPoint BA circQ G ∧
  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine F G FG ∧
  twoLinesIntersectAtPoint DE PQ M ∧
  twoLinesIntersectAtPoint FG PQ N ∧
  distinctPointsOnLine B N BN ∧
  distinctPointsOnLine C M CM ∧
  twoLinesIntersectAtPoint BN CM L ∧
  distinctPointsOnLine A L AL
  → ∠B:A:L = ∠L:A:C
:= by
  sorry

theorem problem_MP49 :
  ∀ (A B C D E F M : Point) (AB BC CA DB DC : Line),
    formTriangle A B C AB BC CA ∧
    (|(A─B)| = |(A─C)|) ∧
    (∠ D:B:C = ∠ A:C:D) ∧
    midpoint B M C ∧
    distinctPointsOnLine D B DB ∧
    distinctPointsOnLine D C DC ∧
    E.onLine DB ∧
    F.onLine DC ∧
    (∠ E:M:F = ∟)
  → 2 * ∠ E:A:F = ∠ B:A:C
:= by
  sorry

theorem problem_imo_2014_p4 :
  ∀ (A B C P Q M N X : Point) (AB BC CA AP AQ BM CN : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    P.onLine BC ∧
    Q.onLine BC ∧
    (∠ P:A:B = ∠ B:C:A) ∧
    (∠ C:A:Q = ∠ A:B:C) ∧
    distinctPointsOnLine A P AP ∧
    M.onLine AP ∧
    midpoint A P M ∧
    distinctPointsOnLine A Q AQ ∧
    N.onLine AQ ∧
    midpoint A Q N ∧
    distinctPointsOnLine B M BM ∧
    distinctPointsOnLine C N CN ∧
    circumCircle Ω A B C ∧
    twoLinesIntersectAtPoint BM CN X
  → X.onCircle Ω :=
by
  sorry

theorem problem_85T22 :
  ∀ (A B C K N M O : Point) (AB BC CA : Line) (circle₁ circle₂ circle₃ : Circle),
    formTriangle A B C AB BC CA ∧
    O.isCentre circle₁ ∧
    A.onCircle circle₁ ∧
    C.onCircle circle₁ ∧
    K.onLine AB ∧
    K.onCircle circle₁ ∧
    between A K B ∧
    N.onLine BC ∧
    N.onCircle circle₁ ∧
    between B N C ∧
    circumCircle circle₂ A B C ∧
    circumCircle circle₃ B K N ∧
    M.onCircle circle₂ ∧
    M.onCircle circle₃ ∧
    M ≠ B
  → ∠ O:M:B = ∟ :=
by
  sorry

theorem problem_10G1 :
  ∀ (A B C D E F P Q : Point)
    (AB BC CA AD BE CF FE BP DF : Line)
    (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  twoLinesIntersectAtPoint AD BC D ∧ perpLine AD BC ∧
  twoLinesIntersectAtPoint BE CA E ∧ perpLine BE CA ∧
  twoLinesIntersectAtPoint CF AB F ∧ perpLine CF AB ∧
  F.onLine FE ∧ E.onLine FE ∧ P.onLine FE ∧
  P.onCircle Ω ∧
  circumCircle Ω A B C ∧
  twoLinesIntersectAtPoint BP DF Q
  → |(A─P)| = |(A─Q)| :=
by
  sorry

theorem problem_MP91 :
  ∀ (A B C D E F O G H : Point) (AB BC CD DA AC BD EO FO HG : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (¬(∃ X : Point, twoLinesIntersectAtPoint AD BC X))
  ∧ distinctPointsOnLine A C AC
  ∧ distinctPointsOnLine B D BD
  ∧ twoLinesIntersectAtPoint AC BD O
  ∧ E.onLine BC
  ∧ F.onLine BC
  ∧ (|(B─E)| = |(C─F)|)
  ∧ distinctPointsOnLine E O EO
  ∧ twoLinesIntersectAtPoint EO CD G
  ∧ distinctPointsOnLine F O FO
  ∧ twoLinesIntersectAtPoint FO BA H
  ∧ distinctPointsOnLine H G HG
  → (¬(∃ X : Point, twoLinesIntersectAtPoint HG AD X))
:= by
  sorry

theorem problem_HP98 :
  ∀ (A B C D E F G : Point) (AB BF FD DA BE CD AG : Line),
  formQuadrilateral A B F D AB BF FD DA ∧
  C.onLine BF ∧ between B C F ∧
  E.onLine FD ∧ between D E F ∧
  ∠B:A:C = ∠D:A:E ∧
  twoLinesIntersectAtPoint BE CD G
  → ∠F:A:C = ∠G:A:E := by
sorry

theorem problem_HP82 :
  ∀ (A B C O D E F G : Point) (AB BC CA DE : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  D.onLine AB ∧
  E.onLine AC ∧
  threePointsOnLine O D E DE ∧
  midpoint B F E ∧
  midpoint C G D
  → ∠F:O:G = ∠B:A:C :=
by
  sorry

theorem problem_07G3 :
∀ (A B C D P Q : Point)
  (AB BC CD DA AC BD : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint AB CD X) ∧
  twoLinesIntersectAtPoint AC BD P ∧
  (∠ A:Q:D = ∠ C:Q:B) ∧
  P.opposingSides Q CD
  → (∠ B:Q:P = ∠ D:A:Q) :=
by
  sorry

theorem problem_imo_2012_p1 :
  ∀ (A B C J M K L F G S T : Point)
    (AB BC CA LM BJ KM CJ AF AG : Line)
    (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  J.isCentre Γ ∧
  tangentAtPoint BC Γ M ∧
  tangentAtPoint AB Γ K ∧
  tangentAtPoint AC Γ L ∧
  distinctPointsOnLine L M LM ∧
  distinctPointsOnLine B J BJ ∧
  twoLinesIntersectAtPoint LM BJ F ∧
  distinctPointsOnLine K M KM ∧
  distinctPointsOnLine C J CJ ∧
  twoLinesIntersectAtPoint KM CJ G ∧
  distinctPointsOnLine A F AF ∧
  twoLinesIntersectAtPoint AF BC S ∧
  distinctPointsOnLine A G AG ∧
  twoLinesIntersectAtPoint AG BC T
  → midpoint S M T
:= by
  sorry

theorem problem_MP1 :
∀ (A B C D E F P : Point) (AB BC CA EB DF : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(A─C)|)
  ∧ (D.onLine AB) ∧ (between A D B)
  ∧ (E.onLine AC) ∧ (between A C E)
  ∧ (|(B─D)| = |(C─E)|)
  ∧ (F.onLine BC) ∧ (between C B F)
  ∧ (|(B─F)| = |(C─B)|)
  ∧ (twoLinesIntersectAtPoint EB DF P)
  → |(P─B)| = |(P─F)| := by
sorry

theorem problem_MP94 :
  ∀ (A B C D P E F G : Point)
    (AB BC CD DA AC BD PE PF FG : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ¬(DA.intersectsLine BC) ∧
    P.onLine BC ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine P E PE ∧
    ¬(PE.intersectsLine AC) ∧
    twoLinesIntersectAtPoint PE AB E ∧
    distinctPointsOnLine P F PF ∧
    distinctPointsOnLine B D BD ∧
    ¬(PF.intersectsLine BD) ∧
    twoLinesIntersectAtPoint PF CD F ∧
    distinctPointsOnLine F G FG ∧
    ¬(FG.intersectsLine BC) ∧
    twoLinesIntersectAtPoint FG AB G
    → |(A─G)| = |(B─E)| :=
by sorry

theorem problem_MP60 :
∀ (A B C D E F : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  D.onLine BC ∧
  perpLine AD BC ∧
  E.onLine AB ∧
  between B A E ∧
  F.onLine AC ∧
  between A F C ∧
  |(A─E)| = |(C─F)|
  → |(E─F)| ≥ |(A─D)| :=
by
  sorry

theorem problem_MP78 :
  ∀ (A B C D E F : Point) (AB BC CA CD AF EF : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(B─C)|)
  ∧ (|(B─C)| = |(C─A)|)
  ∧ distinctPointsOnLine A B AB
  ∧ distinctPointsOnLine B C BC
  ∧ distinctPointsOnLine C A CA
  ∧ distinctPointsOnLine C D CD
  ∧ distinctPointsOnLine A F AF
  ∧ distinctPointsOnLine E F EF
  ∧ between A D B
  ∧ between C B E
  ∧ (|(A─D)| = |(B─E)|)
  ∧ midpoint C F D
  → perpLine AF EF := by
  sorry

theorem problem_HP27 :
  ∀ (A B C D E F G : Point)
    (AB BC CD DA AC BF CE : Line)
    (O₁ O₂ : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  (|(A─B)| = |(A─C)|) ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine C E CE ∧
  circumCircle O₁ A B D ∧
  circumCircle O₂ A C D ∧
  F.onLine AC ∧
  F.onCircle O₁ ∧
  E.onLine AB ∧
  E.onCircle O₂ ∧
  twoLinesIntersectAtPoint BF CE G
  →
  (|(B─G)| * |(C─D)|) = (|(C─G)| * |(B─D)|)
:= by
  sorry

theorem problem_MP50 : ∀
  (A B C D E : Point)
  (AB BC CA AD : Line),
  (formTriangle A B C AB BC CA ∧
   |(A─B)|=|(A─C)| ∧
   D.onLine BC ∧
   distinctPointsOnLine A D AD ∧
   E.onLine AD ∧
   ∠A:D:B = 60 ∧
   |(D─E)|=|(D─B)|)
  → |(C─E)|=|(A─C)| :=
by
  sorry

theorem problem_MP14 :
  ∀ (A B C D E F G : Point) (AB BC CD DA CF : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| = |(B─C)| ∧
    ∠A:B:C = ∠B:C:D ∧
    E.onLine BC ∧
    G.onLine BC ∧
    between B C G ∧
    distinctPointsOnLine C F CF ∧
    ∠D:C:F = ∠F:C:G ∧
    ∠A:E:F = ∠A:B:C
  → |(A─E)| = |(E─F)| := by
  sorry

theorem problem_MP36 :
  ∀ (A B C P : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠ B:A:C = ∟ ∧
    |(A─B)| = |(A─C)| ∧
    insideTriangle P A B C AB BC CA ∧
    ∠ P:B:C = ∟/3 ∧
    ∠ P:C:A = ∟/3
  → ∠ B:A:P = ∟/6
:= by
  sorry

theorem problem_MP4 : ∀ (A B C D : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(B─C)| = |(C─D)| ∧
  ∠B:A:C = ∠C:A:D
  → ∠A:B:C = ∠C:D:A := by
  sorry

theorem problem_HP56 :
∀ (A B C D E F G H I J K L : Point)
  (AB BC CD DA EF FG GH HE IK JL : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(A─B)| = |(B─C)| ∧
  |(B─C)| = |(C─D)| ∧
  |(C─D)| = |(D─A)| ∧
  perpLine AB BC ∧
  perpLine BC CD ∧
  perpLine CD DA ∧
  perpLine DA AB ∧

  formQuadrilateral E F G H EF FG GH HE ∧
  |(E─F)| = |(F─G)| ∧
  |(F─G)| = |(G─H)| ∧
  |(G─H)| = |(H─E)| ∧
  perpLine EF FG ∧
  perpLine FG GH ∧
  perpLine GH HE ∧
  perpLine HE EF ∧

  twoLinesIntersectAtPoint EF AB J ∧
  twoLinesIntersectAtPoint FG BC K ∧
  twoLinesIntersectAtPoint GH CD L ∧
  twoLinesIntersectAtPoint HE DA I ∧
  distinctPointsOnLine I K IK ∧
  distinctPointsOnLine J L JL
  →
  perpLine IK JL
:= by
  sorry

theorem problem_MP38 :
  ∀ (A B C D E : Point) (AB BC CA AD BE : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(A─C)| ∧
    D.onLine BC ∧
    E.onLine CA ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B E BE ∧
    |(A─E)| = |(A─D)| ∧
    |(A─D)| = |(C─D)| ∧
    perpLine AD BE
  → ∠ B : A : C = 100
:= by
  sorry

theorem problem_MP96 :
  ∀ (A B C D P E F G H : Point) (AB BC CD DA PF BF CE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(DA.intersectsLine BC) ∧
  P.onLine DA ∧
  E.onLine AB ∧
  F.onLine CD ∧
  threePointsOnLine P E F PF ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint BF DA H ∧
  twoLinesIntersectAtPoint CE DA G
  → ( |(P─G)| * |(P─H)| = |(P─A)| * |(P─D)| ) :=
by sorry

theorem problem_HP99 :
  ∀ (A B C K D E F M N I J : Point)
    (AB BC CA KB KC : Line)
    (ω₁ ω₂ : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  inCircle ω₁ AB BC CA ∧
  I.isCentre ω₁ ∧
  tangentAtPoint BC ω₁ D ∧
  tangentAtPoint CA ω₁ E ∧
  tangentAtPoint AB ω₁ F ∧
  insideTriangle K A B C AB BC CA ∧
  inCentre J K B C ∧
  inCircle ω₂ KB BC KC ∧
  J.isCentre ω₂ ∧
  tangentAtPoint BC ω₂ D ∧
  tangentAtPoint KB ω₂ M ∧
  tangentAtPoint KC ω₂ N
  → cyclic E F M N :=
by
  sorry

theorem problem_HP28 :
∀ (A B C D E F O : Point)
  (AB BC CA AD EF : Line),
  formTriangle A B C AB BC CA ∧
  insideTriangle D A B C AB BC CA ∧
  circumCentre O A B C ∧
  (∠ D:A:B = ∠ D:C:B) ∧
  (∠ D:A:C = ∠ D:B:C) ∧
  midpoint A E D ∧
  perpLine EF AD ∧
  twoLinesIntersectAtPoint EF BC F
→ (∠ A:F:D = ∠ O:F:C + ∠ O:F:C) :=
by sorry

theorem problem_MP69 :
  ∀ (A B C D P E F : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  threePointsOnLine D A P AD ∧
  E.onLine AB ∧
  F.onLine AC ∧
  |(B─E)|=|(C─F)| ∧
  |(P─E)|=|(P─F)|
  → |(A─B)|=|(A─C)| :=
by sorry

theorem problem_MP13 :
∀ (A B C D E F : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  |(A─B)| = |(A─D)| ∧
  ∠A:B:C = ∟ ∧
  ∠C:D:A = ∟ ∧
  E.onLine BC ∧
  F.onLine CD ∧
  (∠E:A:F + ∠E:A:F = ∠B:A:D)
  → (|(B─E)| + |(D─F)| = |(E─F)|) := by
sorry

theorem problem_12G4 :
  ∀ (A B C D E M O X Y : Point)
    (AB BC CA AD AO DX EY : Line),
    formTriangle A B C AB BC CA ∧
    ¬(|(A─B)| = |(B─C)|) ∧ ¬(|(B─C)| = |(C─A)|) ∧ ¬(|(C─A)| = |(A─B)|) ∧
    circumCentre O A B C ∧
    distinctPointsOnLine A D AD ∧ D.onLine BC ∧ (∠ B:A:D = ∠ D:A:C) ∧
    midpoint B M C ∧ midpoint D M E ∧
    perpLine DX BC ∧ D.onLine DX ∧ X.onLine DX ∧ distinctPointsOnLine A O AO ∧ X.onLine AO ∧
    perpLine EY BC ∧ distinctPointsOnLine E Y EY ∧ E.onLine EY ∧ Y.onLine EY ∧ Y.onLine AD
  → cyclic B X C Y
:= by sorry

theorem problem_13G4 :
  ∀ (A B C P Q D R : Point) (AB BC CA BQ AD : Line) (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| < |(A─C)|) ∧
  P.onLine CA ∧
  Q.onLine CA ∧
  (∠P:B:A = ∠A:C:B) ∧
  (∠Q:B:A = ∠A:C:B) ∧
  between P A C ∧
  distinctPointsOnLine B Q BQ ∧
  D.onLine BQ ∧
  between B D Q ∧
  (|(P─D)| = |(P─B)|) ∧
  circumCircle Ω A B C ∧
  distinctPointsOnLine A D AD ∧
  R.onLine AD ∧
  R.onCircle Ω
  → (|(Q─B)| = |(Q─R)|) := by
  sorry

theorem problem_HP50 :
  ∀ (A B C I M : Point) (AB BC CA : Line) (O₁ O₂ : Circle),
    formTriangle A B C AB BC CA ∧
    inCentre I A B C ∧
    tangentLine AB O₁ ∧
    tangentLine BC O₁ ∧
    A.onCircle O₂ ∧
    C.onCircle O₂ ∧
    M.onCircle O₁ ∧
    M.onCircle O₂ ∧
    ¬(O₁.intersectsCircle  O₂)
  → ∠ A:M:I = ∠ I:M:C
:= by
  sorry

theorem HP78 :
∀ (A B C D E F G H : Point)
  (AB BC CD DA AC BD BG CG EF GH : Line),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D A DA ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine B G BG ∧
  distinctPointsOnLine C G CG ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine G H GH ∧
  formQuadrilateral A B C D AB BC CD DA ∧
  midpoint A E D ∧
  midpoint B F C ∧
  twoLinesIntersectAtPoint AC BD H ∧
  ¬(BG.intersectsLine CD) ∧
  ¬(CG.intersectsLine AB)
  → ¬(GH.intersectsLine EF) :=
by sorry

theorem problem_HP53 :
  ∀ (A B C D E F M N O K : Point)
    (AB BC CA AD EM FN BN CM OKLine AKLine : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  midpoint C E A ∧
  midpoint A F B ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine E M EM ∧
  perpLine EM CA ∧
  twoLinesIntersectAtPoint AD EM M ∧
  distinctPointsOnLine F N FN ∧
  perpLine FN AB ∧
  twoLinesIntersectAtPoint AD FN N ∧
  twoLinesIntersectAtPoint EM FN O ∧
  distinctPointsOnLine C M CM ∧
  distinctPointsOnLine B N BN ∧
  twoLinesIntersectAtPoint CM BN K ∧
  distinctPointsOnLine O K OKLine ∧
  distinctPointsOnLine A K AKLine
  → perpLine OKLine AKLine := by
  sorry

theorem problem_imo_2009_p2 : ∀
(A B C O P Q K L M : Point) (AB BC CA PQ : Line) (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  between C P A ∧
  between A Q B ∧
  midpoint B K P ∧
  midpoint C L Q ∧
  midpoint P M Q ∧
  threePointsOnLine P Q M PQ ∧
  K.onCircle Γ ∧
  L.onCircle Γ ∧
  M.onCircle Γ ∧
  tangentAtPoint PQ Γ M
  → |(O─P)| = |(O─Q)| := by
sorry

theorem problem_HP74 :
  ∀ (A B C D E F G O : Point)
    (AB BC CD DA AC BD CE DF FE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  twoLinesIntersectAtPoint AC BD O ∧
  twoLinesIntersectAtPoint CE BD E ∧
  perpLine CE BD ∧
  twoLinesIntersectAtPoint DF AC F ∧
  perpLine DF AC ∧
  twoLinesIntersectAtPoint FE AB G
  → perpLine GO AD
:= by
  sorry

theorem problem_imo_2010_p4 :
  ∀ (A B C P K L M S : Point) (AB BC CA AP BP CP cT : Line) (Γ : Circle),
    formTriangle A B C AB BC CA ∧
    insideTriangle P A B C AB BC CA ∧
    ¬(|(C─A)| = |(C─B)|) ∧
    circumCircle Γ A B C ∧
    A.onLine AP ∧ P.onLine AP ∧ K.onLine AP ∧
    B.onLine BP ∧ P.onLine BP ∧ L.onLine BP ∧
    C.onLine CP ∧ P.onLine CP ∧ M.onLine CP ∧
    K.onCircle Γ ∧ L.onCircle Γ ∧ M.onCircle Γ ∧
    tangentAtPoint cT Γ C ∧
    twoLinesIntersectAtPoint AB cT S ∧
    |(S─C)| = |(S─P)|
  → |(M─K)| = |(M─L)| :=
by sorry

theorem problem_MP16 :
∀ (A B C D E F : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠ A:C:B = ∟ ∧
  ∠ B:A:C = 30 ∧
  D.onLine CA ∧
  E.onLine AB ∧
  F.onLine BC ∧
  |(A─E)| = |(A─C)| ∧
  ∠ B:A:F = ∠ F:A:C ∧
  |(C─D)| = |(C─F)|
  → ∠ C:E:D = 15 := by
sorry

theorem problem_HP81 :
  ∀ (A B C I D E F : Point) (AB BC CA : Line) (O J : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  inCentre I A B C ∧
  tangentAtPoint AB J D ∧
  tangentAtPoint AC J E ∧
  F.onCircle O ∧
  F.onCircle J ∧
  (∀ (P : Point), P.onCircle O ∧ P.onCircle J → P = F)
  → ∠B:F:I = ∠I:F:C
:= by
  sorry

theorem problem_HP93 :
∀ (A B C P D E F : Point) (AB BC CA PD PE PF DE : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  P.onCircle O ∧
  distinctPointsOnLine P D PD ∧
  twoLinesIntersectAtPoint PD BC D ∧
  perpLine PD BC ∧
  distinctPointsOnLine P E PE ∧
  twoLinesIntersectAtPoint PE CA E ∧
  perpLine PE CA ∧
  distinctPointsOnLine P F PF ∧
  twoLinesIntersectAtPoint PF AB F ∧
  perpLine PF AB ∧
  distinctPointsOnLine D E DE
→ threePointsOnLine D E F DE :=
by sorry

theorem problem_MP5 :
∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ¬ (|(A─B)| = |(A─C)|) ∧
  (|(D─B)| = |(D─C)|) ∧
  (∠B:A:D = ∠D:A:C)
  → ∠A:B:D = ∠A:C:D := by
sorry

theorem problem_MP29 :
∀ (A B C D E F : Point)
(AB BC CA CD DA BD CE : Line),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| = |(A─C)|) ∧
  formTriangle A C D CA CD DA ∧
  (|(A─C)| = |(A─D)|) ∧
  (∠C:A:D = ∟) ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint BD CA F ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint AD CE E ∧
  ¬(AB.intersectsLine CE)
→ |(A─E)| + |(A─F)| = |(C─E)| := by
  sorry

theorem problem_HP31 :
∀ (A B C D E F G O : Point)
  (AB BC CD DA FG : Line)
  (circleO : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  O.isCentre circleO ∧
  A.onCircle circleO ∧ B.onCircle circleO ∧ C.onCircle circleO ∧ D.onCircle circleO ∧
  insideQuadrilateral E A B C D AB BC CD DA ∧
  ∠ E:A:B = ∠ E:C:O ∧
  ∠ E:B:A = ∠ E:D:C ∧
  distinctPointsOnLine F G FG ∧
  E.onLine FG ∧
  ∠ B:E:F = ∠ F:E:C ∧
  F.onCircle circleO ∧
  G.onCircle circleO
→ |(E─F)| = |(E─G)| :=
by sorry

theorem problem_MP82 :
∀ (A B C D E : Point) (AB BC CA : Line),
  (formTriangle A B C AB BC CA)
  ∧ threePointsOnLine B C E BC
  ∧ threePointsOnLine B C D BC
  ∧ between B C E
  ∧ between C B D
  ∧ ( ∠A:B:D = ( ∠A:C:E + ∠A:C:E ) )
  →
  ( (|(A─B)| * |(A─B)| - |(A─C)| * |(A─C)|) = (|(B─C)| * |(A─B)|) )
:= by
  sorry

theorem problem_imo_2018_p1 :
∀ (A B C D E F G : Point) (AB BC CA L_F L_G DE FG : Line) (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine F G FG ∧
  D.onLine AB ∧ E.onLine AC ∧
  between A D B ∧ between A E C ∧
  |(A─D)| = |(A─E)| ∧
  perpBisector B D L_F ∧ F.onLine L_F ∧ F.onCircle Γ ∧
  perpBisector C E L_G ∧ G.onLine L_G ∧ G.onCircle Γ
  → (¬(DE.intersectsLine FG) ∨ (∀ X : Point, X.onLine DE ↔ X.onLine FG))
:= by
  sorry

theorem problem_19G4 :
  ∀ (A B C P A1 B1 C1 A2 B2 C2 : Point) (AB BC CA AP BP CP : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    insideTriangle P A B C AB BC CA ∧
    distinctPointsOnLine A P AP ∧
    distinctPointsOnLine B P BP ∧
    distinctPointsOnLine C P CP ∧
    twoLinesIntersectAtPoint AP BC A1 ∧
    twoLinesIntersectAtPoint BP CA B1 ∧
    twoLinesIntersectAtPoint CP AB C1 ∧
    midpoint P A1 A2 ∧
    midpoint P B1 B2 ∧
    midpoint P C1 C2 ∧
    circumCircle Ω A B C
  → ¬(A2.insideCircle Ω ∧ B2.insideCircle Ω ∧ C2.insideCircle Ω) :=
by sorry

theorem problem_HP14 :
  ∀ (A B C D E F O P : Point)
    (L1 L2 L3 L4 L5 L6 : Line)
    (C1 C2 : Circle),
  O.isCentre C1 ∧
  P.isCentre C2 ∧
  A.onCircle C1 ∧
  B.onCircle C1 ∧
  A.onCircle C2 ∧
  B.onCircle C2 ∧
  distinctPointsOnLine B O L1 ∧
  distinctPointsOnLine P A L2 ∧
  twoLinesIntersectAtPoint L1 L2 C ∧
  distinctPointsOnLine C D L3 ∧
  tangentAtPoint L3 C1 D ∧
  distinctPointsOnLine C E L4 ∧
  tangentAtPoint L4 C2 E ∧
  distinctPointsOnLine D E L5 ∧
  distinctPointsOnLine A B L6 ∧
  twoLinesIntersectAtPoint L5 L6 F
  → midpoint D F E := by
  sorry

theorem problem_MP55 : ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  midpoint A D B ∧
  E.onLine CA ∧
  ( ∠A:E:D + ∠A:E:D = ∠A:C:B )
  → |(A─E)| = |(B─C)| + |(C─E)| := by
  sorry

theorem problem_MP37 :
∀ (A B C D E : Point)
  (AB BC CA DE : Line),
  formTriangle A B C AB BC CA
  ∧ ∠ B:A:C = 20
  ∧ |(A─B)| = |(A─C)|
  ∧ D.onLine BC
  ∧ between B C D
  ∧ |(B─D)| = |(A─B)|
  ∧ distinctPointsOnLine D E DE
  ∧ ¬(∃ P : Point, twoLinesIntersectAtPoint DE AB P)
  ∧ twoLinesIntersectAtPoint DE CA E
  ∧ between A C E
  → ∠ B:E:D = 30
:= by
  sorry

theorem problem_HP8 :
∀ (A B C D E F P : Point)
  (AB BC CA AD DF DE BF CE AP : Line),
  formTriangle A B C AB BC CA ∧
  twoLinesIntersectAtPoint AD BC D ∧
  ∠B:A:D = ∠D:A:C ∧
  twoLinesIntersectAtPoint DF CA F ∧
  perpLine DF CA ∧
  twoLinesIntersectAtPoint DE AB E ∧
  perpLine DE AB ∧
  twoLinesIntersectAtPoint CE BF P ∧
  distinctPointsOnLine A P AP
  → perpLine AP BC := by
  sorry

theorem problem_MP99 :
∀ (A B C D E F G H : Point)
  (AB BC CD DA AG CF BH EG : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (¬ ∃ X : Point, twoLinesIntersectAtPoint AB DC X) ∧
  (¬ ∃ X : Point, twoLinesIntersectAtPoint BC AD X) ∧
  between B E C ∧
  between D F A ∧
  |(B─E)| = |(D─F)| ∧
  G.onLine CD ∧
  distinctPointsOnLine A G AG ∧
  distinctPointsOnLine C F CF ∧
  twoLinesIntersectAtPoint AG CF H ∧
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine E G EG
→ (¬ ∃ X : Point, twoLinesIntersectAtPoint BH EG X) :=
by sorry

theorem problem_91T1 :
∀ (A B C P D E F M N X : Point)
  (AB BC CA BP CP PD PE PF AM AN ME NF : Line),
  (
    formTriangle A B C AB BC CA
    ∧ insideTriangle P A B C AB BC CA
    ∧ distinctPointsOnLine B P BP
    ∧ distinctPointsOnLine C P CP
    ∧ distinctPointsOnLine P D PD
    ∧ D.onLine BC
    ∧ perpLine PD BC
    ∧ distinctPointsOnLine P E PE
    ∧ E.onLine CA
    ∧ perpLine PE CA
    ∧ distinctPointsOnLine P F PF
    ∧ F.onLine AB
    ∧ perpLine PF AB
    ∧ distinctPointsOnLine A M AM
    ∧ M.onLine BP
    ∧ perpLine AM BP
    ∧ distinctPointsOnLine A N AN
    ∧ N.onLine CP
    ∧ perpLine AN CP
    ∧ distinctPointsOnLine M E ME
    ∧ distinctPointsOnLine N F NF
  )
  → (
    twoLinesIntersectAtPoint ME NF X
    ∧ X.onLine BC
  )
:= by
  sorry

theorem problem_HP15 :
  ∀ (A B C D E F G : Point) (CD CB DB L1 L2 : Line) (O P : Circle),
  O.intersectsCircle P ∧
  A.onCircle O ∧ A.onCircle P ∧
  B.onCircle O ∧ B.onCircle P ∧
  threePointsOnLine A C D CD ∧
  C.onCircle O ∧
  D.onCircle P ∧
  threePointsOnLine C B F CB ∧
  F.onCircle P ∧
  threePointsOnLine D B E DB ∧
  E.onCircle O ∧
  A.onLine L1 ∧
  perpLine L1 CD ∧
  perpBisector E F L2 ∧
  twoLinesIntersectAtPoint L1 L2 G
  → (|(A─G)| * |(A─G)| = |(E─G)| * |(E─G)| + (|(A─C)| * |(A─D)|)) := by
  sorry

theorem problem_HP89 :
  ∀ (A B C D E F G M N : Point) (O : Circle)
    (AB BC CA L AD FG EG MN : Line),
  (formTriangle A B C AB BC CA)
  ∧ circumCircle O A B C
  ∧ perpBisector B C L
  ∧ twoLinesIntersectAtPoint L BC F
  ∧ D.onLine L ∧ D.onCircle O
  ∧ E.onLine L ∧ E.onCircle O
  ∧ distinctPointsOnLine A D AD
  ∧ F.onLine FG ∧ G.onLine FG
  ∧ ¬(∃ X : Point, twoLinesIntersectAtPoint FG AD X)
  ∧ distinctPointsOnLine E G EG
  ∧ twoLinesIntersectAtPoint MN AB M
  ∧ twoLinesIntersectAtPoint MN AC N
  ∧ perpLine MN EG
  → |(G─M)| = |(G─N)| :=
by
  sorry

theorem problem_HP92 :
∀ (A B C D M E F O : Point)
  (AB BC CA AD PBD PCD : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine BC ∧
  distinctPointsOnLine A D AD ∧
  perpLine AD BC ∧
  midpoint B M C ∧
  perpBisector B D PBD ∧
  F.onLine PBD ∧
  F.onLine AB ∧
  perpBisector C D PCD ∧
  E.onLine PCD ∧
  E.onLine AC ∧
  O.onLine PBD ∧
  O.onLine PCD
→ cyclic A F O E := by
  sorry

theorem problem_HP12 :
  ∀ (A B C D O P E F : Point) (CD CA AD PO t : Line) (Γ : Circle),
    O.isCentre Γ ∧
    A.onCircle Γ ∧
    B.onCircle Γ ∧
    C.onCircle Γ ∧
    D.onCircle Γ ∧
    distinctPointsOnLine C D CD ∧
    distinctPointsOnLine C A CA ∧
    distinctPointsOnLine A D AD ∧
    tangentAtPoint t Γ B ∧
    twoLinesIntersectAtPoint t CD P ∧
    distinctPointsOnLine P O PO ∧
    twoLinesIntersectAtPoint PO CA E ∧
    twoLinesIntersectAtPoint PO AD F
  → |(O─E)| = |(O─F)| :=
by
  sorry

theorem problem_MP40 :
  ∀ (A B C D E : Point) (AB BC CA DE : Line),
    formTriangle A B C AB BC CA ∧
    ∠B:A:C = 100 ∧
    |(A─B)| = |(A─C)| ∧
    D.onLine BC ∧
    |(B─D)| = |(A─B)| ∧
    distinctPointsOnLine D E DE ∧
    twoLinesIntersectAtPoint DE CA E ∧
    ¬(DE.intersectsLine AB)
    → ∠B:E:D = 30 := by
  sorry

theorem problem_HP75 :
∀ (A B C D E F G : Point) (AB BC CA BD CE : Line) (O P : Circle),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C = ∟) ∧
  E.onLine AB ∧
  distinctPointsOnLine C E CE ∧
  D.onLine CA ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint BD CE F ∧
  circumCircle O A B C ∧
  circumCircle P A E D ∧
  G.onCircle O ∧
  G.onCircle P
  → ∠A:G:F = ∟
:= by
  sorry

theorem problem_imo_2008_p6 :
  ∀ (A B C D : Point) (AB BC CD DA AC : Line) (ω₁ ω₂ ω : Circle) (L₁ L₂ : Line) (P : Point),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(B─A)| ≠ |(B─C)| ∧
    inCircle ω₁ AB BC AC ∧
    inCircle ω₂ AD DC AC ∧
    tangentLine AB ω ∧
    tangentLine BC ω ∧
    tangentLine AD ω ∧
    tangentLine CD ω ∧
    tangentLine L₁ ω₁ ∧
    tangentLine L₁ ω₂ ∧
    tangentLine L₂ ω₁ ∧
    tangentLine L₂ ω₂ ∧
    twoLinesIntersectAtPoint L₁ L₂ P
    → P.onCircle ω := by
  sorry

theorem problem_HP32 :
∀ (A B C D E F P L M N G : Point) (AB BC CA AD BE CF : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D AD ∧ D.onLine BC ∧ perpLine AD BC ∧
  distinctPointsOnLine B E BE ∧ E.onLine CA ∧ perpLine BE CA ∧
  distinctPointsOnLine C F CF ∧ F.onLine AB ∧ perpLine CF AB ∧
  insideTriangle P A B C AB BC CA ∧
  perpBisector P L BC ∧
  perpBisector P M CA ∧
  perpBisector P N AB ∧
  midpoint A G P
  → ((cyclic D E G F) → (cyclic A M L N)) ∧ ((cyclic A M L N) → (cyclic D E G F)) := by
sorry

theorem problem_MP17 :
  ∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  (∠ A:B:C = ∠ A:C:B + ∠ A:C:B) ∧
  (∠ B:A:D = ∠ C:A:D + ∠ C:A:D)
  → ∠ B:A:C = ∟ :=
by
  sorry

theorem problem_MP59 :
  ∀ (A B C D E F H : Point) (AB BC CA AD BF DH : Line),
    formTriangle A B C AB BC CA ∧
    distinctPointsOnLine A D AD ∧
    midpoint B D C ∧
    midpoint A E C ∧
    midpoint A F D ∧
    distinctPointsOnLine B F BF ∧
    distinctPointsOnLine D H DH ∧
    twoLinesIntersectAtPoint DH BF H ∧
    perpLine DH BF
  → True := by
  sorry

theorem problem_MP63 :
  ∀ (A B C D E F G : Point)
    (AB BC CD DE EA AF BG AG EF : Line),
    formPentagon A B C D E AB BC CD DE EA ∧
    ∠A:B:C = ∟ ∧
    ∠A:E:D = ∟ ∧
    F.onLine BC ∧
    G.onLine DE ∧
    distinctPointsOnLine A F AF ∧
    distinctPointsOnLine B G BG ∧
    distinctPointsOnLine A G AG ∧
    distinctPointsOnLine E F EF ∧
    perpLine AF BG ∧
    perpLine AG EF
  → |(A─B)| = |(A─E)| :=
by
  sorry

theorem problem_HP47 :
  ∀ (A B C D E F G H O : Point)
    (BC AO AD CO FO CG : Line)
    (Ω : Circle),
  (O.isCentre Ω ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω) ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine C O CO ∧
  distinctPointsOnLine F O FO ∧
  distinctPointsOnLine C G CG ∧
  distinctPointsOnLine A O AO ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC ∧
  twoLinesIntersectAtPoint AD CO E ∧
  midpoint A F E ∧
  twoLinesIntersectAtPoint FO BC H ∧
  perpLine CG AO ∧
  twoLinesIntersectAtPoint CG AO G
  → cyclic B H O G :=
by
  sorry

theorem problem_imo_2008_p1 :
∀ (A B C H A_1 A_2 B_1 B_2 C_1 C_2 M_BC M_CA M_AB : Point)
  (AB BC CA AH BH CH : Line)
  (α β γ : Circle),
  (formTriangle A B C AB BC CA)
  ∧ (∠A:B:C < ∟)
  ∧ (∠B:C:A < ∟)
  ∧ (∠C:A:B < ∟)
  ∧ distinctPointsOnLine A H AH
  ∧ distinctPointsOnLine B H BH
  ∧ distinctPointsOnLine C H CH
  ∧ perpLine AH BC
  ∧ perpLine BH CA
  ∧ perpLine CH AB
  ∧ midpoint B M_BC C
  ∧ M_BC.isCentre α
  ∧ H.onCircle α
  ∧ A_1.onLine BC
  ∧ A_1.onCircle α
  ∧ A_2.onLine BC
  ∧ A_2.onCircle α
  ∧ midpoint C M_CA A
  ∧ M_CA.isCentre β
  ∧ H.onCircle β
  ∧ B_1.onLine CA
  ∧ B_1.onCircle β
  ∧ B_2.onLine CA
  ∧ B_2.onCircle β
  ∧ midpoint A M_AB B
  ∧ M_AB.isCentre γ
  ∧ H.onCircle γ
  ∧ C_1.onLine AB
  ∧ C_1.onCircle γ
  ∧ C_2.onLine AB
  ∧ C_2.onCircle γ
→ ∃ δ : Circle,
    A_1.onCircle δ
    ∧ A_2.onCircle δ
    ∧ B_1.onCircle δ
    ∧ B_2.onCircle δ
    ∧ C_1.onCircle δ
    ∧ C_2.onCircle δ
:= by
  sorry

theorem problem_HP4 :
  ∀ (A B C D E X Y J : Point)
    (AB BC CA AD AY BE BX : Line)
    (Γ Ω : Circle),
  formTriangle A B C AB BC CA ∧
  ∠B:A:C = ∟ ∧
  circumCircle Γ A B C ∧
  tangentAtPoint AD Γ A ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpBisector A E BC ∧
  distinctPointsOnLine A Y AY ∧
  distinctPointsOnLine B E BE ∧
  perpLine AY BE ∧
  twoLinesIntersectAtPoint AY BE Y ∧
  midpoint A X Y ∧
  distinctPointsOnLine B X BX ∧
  J.onLine BX ∧
  J.onCircle Γ ∧
  circumCircle Ω A J D
  → tangentAtPoint BD Ω D
:= by
  sorry

theorem problem_MP25 :
  ∀ (A B C D E : Point) (AB BC CA DE : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  threePointsOnLine A B D AB ∧
  between A B D ∧
  distinctPointsOnLine D E DE ∧
  twoLinesIntersectAtPoint DE CA E ∧
  perpLine DE CA ∧
  ∠C:D:E = ∠A:B:C
  → (|(B─D)| = |(A─E)| + |(A─E)|)
:= by
  sorry

theorem problem_16G4 :
  ∀ (A B C I I' D E : Point)
    (AB BC CA BI AI DE : Line),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C < ∟) ∧
  (∠A:B:C < ∟) ∧
  (∠A:C:B < ∟) ∧
  (|(A─B)| = |(A─C)|) ∧
  (|(A─B)| ≠ |(B─C)|) ∧
  inCentre I A B C ∧
  twoLinesIntersectAtPoint BI CA D ∧
  perpLine DE CA ∧
  twoLinesIntersectAtPoint DE AI E ∧
  perpBisector I I' CA
  → cyclic B D E I' :=
by
  sorry

theorem problem_imo_2004_p1 :
∀ (A B C M N O R : Point) (AB BC CA : Line) (ω γ δ : Circle),
  (formTriangle A B C AB BC CA)
∧ ( |(A─B)| ≠ |(A─C)| )
∧ midpoint B O C
∧ O.isCentre ω
∧ B.onCircle ω
∧ C.onCircle ω
∧ M.onLine AB
∧ M.onCircle ω
∧ (M ≠ A)
∧ (M ≠ B)
∧ N.onLine AC
∧ N.onCircle ω
∧ (N ≠ A)
∧ (N ≠ C)
∧ ( ∠B:A:R = ∠R:A:C )
∧ ( ∠M:O:R = ∠R:O:N )
∧ circumCircle γ B M R
∧ circumCircle δ C N R
→ ∃ X : Point, X.onLine BC ∧ X.onCircle γ ∧ X.onCircle δ :=
by sorry

theorem problem_16G7 :
∀ (A B C I I_A I_A' I_B I_B' P : Point)
  (AB BC CA AI l_A l_B : Line),
  (
    formTriangle A B C AB BC CA
    ∧ ¬ ( (|(A─B)| = |(B─C)|) ∨ (|(B─C)| = |(C─A)|) ∨ (|(C─A)| = |(A─B)|) )
    ∧ inCentre I A B C
    -- No provided axiom for “I_A is the excenter opposite A”.
    -- No provided axiom for reflections “I_A' across line BC” or “l_A across line AI”.
    -- Same definitions assumed for I_B, I_B', and l_B.
    ∧ twoLinesIntersectAtPoint l_A l_B P
  )
  → True
:= by
  sorry

theorem problem_MP45 :
  ∀ (A B C I E F D K M : Point)
    (AB BC CA BI CI EF AD IM : Line),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  distinctPointsOnLine B I BI ∧
  E.onLine BI ∧
  between B I E ∧
  distinctPointsOnLine C I CI ∧
  F.onLine CI ∧
  between C I F ∧
  (|(A─E)| = |(A─I)|) ∧
  (|(A─I)| = |(A─F)|) ∧
  distinctPointsOnLine A D AD ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint AD EF K ∧
  distinctPointsOnLine I M IM ∧
  twoLinesIntersectAtPoint IM BC M ∧
  perpLine IM BC
  → |(A─K)| = |(I─M)| := by
  sorry

theorem problem_00G2 :
∀ (A B C D E M N P Q : Point)
  (AB AC BD AN BN CD : Line)
  (G1 G2 : Circle),
  M.onCircle G1 ∧ M.onCircle G2 ∧ N.onCircle G1 ∧ N.onCircle G2 ∧ M ≠ N ∧
  A.onLine AB ∧ B.onLine AB ∧ tangentAtPoint AB G1 A ∧ tangentAtPoint AB G2 B ∧
  (∀ T : Point, twoLinesIntersectAtPoint AB CD T → false) ∧
  M.onLine CD ∧ C.onLine CD ∧ C.onCircle G1 ∧ D.onLine CD ∧ D.onCircle G2 ∧
  A.onLine AC ∧ C.onLine AC ∧ B.onLine BD ∧ D.onLine BD ∧ twoLinesIntersectAtPoint AC BD E ∧
  A.onLine AN ∧ N.onLine AN ∧ twoLinesIntersectAtPoint AN CD P ∧
  B.onLine BN ∧ N.onLine BN ∧ twoLinesIntersectAtPoint BN CD Q
  → |(E─P)| = |(E─Q)| :=
by sorry

theorem problem_HP76 :
∀ (A B C D E F P G H I J K L M : Point)
  (AB BC CA AD BE CF GKLine HLLine IJLine : Line),
  formTriangle A B C AB BC CA ∧
  D.onLine BC ∧
  E.onLine CA ∧
  F.onLine AB ∧
  twoLinesIntersectAtPoint AD CF P ∧
  twoLinesIntersectAtPoint BE CF P ∧
  midpoint B G C ∧
  midpoint C H A ∧
  midpoint A I B ∧
  midpoint D J E ∧
  midpoint E K F ∧
  midpoint F L D ∧
  distinctPointsOnLine G K GKLine ∧
  distinctPointsOnLine H L HLLine ∧
  distinctPointsOnLine I J IJLine
  → twoLinesIntersectAtPoint GKLine HLLine M ∧ M.onLine IJLine
:= by
  sorry

theorem problem_HP80 :
  ∀ (A B C D E F L M N : Point) (AC BD EF LMN : Line),
  midpoint A L C ∧
  midpoint B M D ∧
  midpoint E N F
  → threePointsOnLine L M N LMN
:= by
  sorry

theorem problem_imo_2011_p6 :
∀ (A B C P Q R : Point)
  (AB BC CA ℓ ℓ_a ℓ_b ℓ_c : Line)
  (Γ circ : Circle),
  formTriangle A B C AB BC CA ∧
  A.outsideCircle Γ ∧ B.outsideCircle Γ ∧ C.outsideCircle Γ ∧
  tangentLine ℓ Γ ∧
  -- Below we acknowledge the reflective constructions as assumptions
  -- (no built-in predicate for reflection is provided, so we treat them as given)
  -- “ℓ_a, ℓ_b, ℓ_c are the reflections of ℓ about BC, CA, and AB”
  -- represented here as extra assumptions:
  (ℓ_a ≠ ℓ ∧ ℓ_b ≠ ℓ ∧ ℓ_c ≠ ℓ) ∧
  (¬(ℓ_a.intersectsLine BC) ∧ ¬(ℓ_b.intersectsLine CA) ∧ ¬(ℓ_c.intersectsLine AB)) ∧
  twoLinesIntersectAtPoint ℓ_a ℓ_b P ∧
  twoLinesIntersectAtPoint ℓ_b ℓ_c Q ∧
  twoLinesIntersectAtPoint ℓ_c ℓ_a R ∧
  formTriangle P Q R ℓ_a ℓ_b ℓ_c ∧
  circumCircle circ P Q R
→
  -- Expressing “circ is tangent to Γ” as:
  -- exactly one point of intersection plus the fact that they do intersect
  (∃ T : Point,
    T.onCircle circ ∧ T.onCircle Γ ∧
    ∀ X, X.onCircle circ ∧ X.onCircle Γ → X = T)
  ∧ circ.intersectsCircle  Γ
:= by
  sorry

theorem problem_HP62 :
  ∀ (A B C D E F G K : Point) (AB BC CD DA EF AG : Line) (O : Circle),
  (
    formQuadrilateral A B C D AB BC CD DA
    ∧ A.onCircle O
    ∧ B.onCircle O
    ∧ C.onCircle O
    ∧ D.onCircle O
    ∧ twoLinesIntersectAtPoint AB CD E
    ∧ twoLinesIntersectAtPoint AD BC F
    ∧ distinctPointsOnLine E F EF
    ∧ midpoint E G F
    ∧ distinctPointsOnLine A G AG
    ∧ K.onLine AG
    ∧ K.onCircle O
  )
  → cyclic C K F E
:= by sorry

theorem problem_HP54 :
  ∀ (A B C D E F O : Point)
    (AB BC CA DA CE FO : Line)
    (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  A.onCircle Ω ∧
  C.onCircle Ω ∧
  O.isCentre Ω ∧
  distinctPointsOnLine D A DA ∧
  tangentAtPoint DA Ω A ∧
  E.onLine AB ∧
  E.onCircle Ω ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint CE DA F ∧
  distinctPointsOnLine F O FO
  → perpLine FO BC := by
  sorry

theorem problem_04G1 :
∀ (A B C M N O R : Point) (AB BC CA : Line) (circle1 circle2 circle3 : Circle),
  (formTriangle A B C AB BC CA ∧
   |(A─B)| ≠ |(A─C)| ∧
   M.onLine AB ∧
   N.onLine AC ∧
   midpoint B O C ∧
   O.isCentre circle1 ∧
   B.onCircle circle1 ∧
   C.onCircle circle1 ∧
   M.onCircle circle1 ∧
   N.onCircle circle1 ∧
   ∠B:A:R = ∠R:A:C ∧
   ∠M:O:R = ∠R:O:N ∧
   circumCircle circle2 B M R ∧
   circumCircle circle3 C N R)
  → ∃ X : Point, X.onLine BC ∧ X.onCircle circle2 ∧ X.onCircle circle3
:= by
  sorry

theorem problem_HP49 :
∀ (A B C H D E : Point) (AB BC CA AH BH CH AD BE : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A H AH ∧
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine C H CH ∧
  twoLinesIntersectAtPoint AH BH H ∧
  H.onLine CH ∧
  perpLine AH BC ∧
  perpLine BH AC ∧
  perpLine CH AB ∧
  midpoint C D H ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine B E BE ∧
  twoLinesIntersectAtPoint AD BE E ∧
  perpLine AD BE
  → cyclic B C E H :=
by sorry

theorem problem_MP43 :
  ∀ (A B C D E : Point) (AB BC CA BD : Line),
    (formTriangle A B C AB BC CA ∧
     |(A─B)| = |(A─C)| ∧
     D.onLine AC ∧
     E.onLine BD ∧
     ∠A:D:B = 60 ∧
     |(C─E)| = |(C─B)|)
  → ∠A:E:C = 30 :=
by
  sorry

theorem problem_HP94 :
  ∀ (A B C D E F P : Point) (AB CD EF : Line) (O : Circle),
  A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O ∧ E.onCircle O ∧ F.onCircle O ∧
  twoLinesIntersectAtPoint AB CD P ∧ twoLinesIntersectAtPoint AB EF P ∧ twoLinesIntersectAtPoint CD EF P ∧
  ∠B:P:D = 60 ∧ ∠D:P:F = 60 ∧ ∠F:P:B = 60
  → |(A─P)| + |(E─P)| + |(D─P)| = |(C─P)| + |(B─P)| + |(F─P)| := by
  sorry

theorem problem_imo_2000_p1 :
∀ (G₁ G₂ : Circle)
  (A B C D E M N P Q : Point)
  (AB AC BD AN BN CD : Line),
  (M.onCircle G₁ ∧ M.onCircle G₂) ∧
  (N.onCircle G₁ ∧ N.onCircle G₂) ∧
  (A.onCircle G₁ ∧ A.onLine AB) ∧
  (B.onCircle G₂ ∧ B.onLine AB) ∧
  tangentAtPoint AB G₁ A ∧
  tangentAtPoint AB G₂ B ∧
  M.onLine CD ∧
  (¬(∃ X : Point, twoLinesIntersectAtPoint AB CD X)) ∧
  (C.onCircle G₁ ∧ C.onLine CD) ∧
  (D.onCircle G₂ ∧ D.onLine CD) ∧
  twoLinesIntersectAtPoint AC BD E ∧
  twoLinesIntersectAtPoint AN CD P ∧
  twoLinesIntersectAtPoint BN CD Q
  → |(E─P)| = |(E─Q)|
:= by
  sorry

theorem problem_HP72 :
∀ (A B C D E F G H I O : Point)
  (AB BC CD DA AC BD EF GI AO AI : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  twoLinesIntersectAtPoint AC BD G ∧
  midpoint A E B ∧
  midpoint C F D ∧
  /- Orthocenter conditions (not expressible with given axioms) for H in triangle AGD and for I in triangle BGC -/
  twoLinesIntersectAtPoint EF GI I ∧
  distinctPointsOnLine A I AI ∧
  distinctPointsOnLine A O AO
  → perpLine AI AO :=
by sorry

theorem problem_HP96 : ∀
  (A B C D : Point)
  (AB BC CD DA : Line)
  (O : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  A.onCircle O ∧
  B.onCircle O ∧
  C.onCircle O ∧
  D.onCircle O
  → ( |(A─B)| * |(C─D)| + |(A─D)| * |(B─C)| = |(A─C)| * |(B─D)| )
:= by
  sorry

theorem problem_HP91 :
∀
(A B C D E F G : Point)
(BC BA AD DE DF EF : Line)
(O : Circle),
  circumCircle O A B C ∧
  (∠B:A:C = ∟) ∧
  D.onCircle O ∧
  A.opposingSides D BC ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine B A BA ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine D F DF ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint DE BC E ∧
  perpLine DE BC ∧
  twoLinesIntersectAtPoint DF BA F ∧
  perpLine DF BA ∧
  twoLinesIntersectAtPoint EF AD G
→ midpoint A G D
:= by
  sorry

theorem problem_MP31 : ∀
(A B C D E : Point)
(AB BC CA : Line),
formTriangle A B C AB BC CA ∧
between B D C ∧
between A C E ∧
|(A─C)| = |(A─B)| ∧
|(A─B)| = |(B─D)| ∧
|(B─D)| = |(D─E)| ∧
|(C─D)| = |(C─E)|
→ ∠ B : A : C = 100
:= by
  sorry

theorem HP18 :
∀ (A B C D E F G H : Point)
  (BA CD EC ED FG AH : Line)
  (P Q : Circle),
  (A.onCircle P) ∧ (B.onCircle P) ∧ (A.onCircle Q) ∧ (B.onCircle Q) ∧ P.intersectsCircle Q ∧
  tangentAtPoint CD P C ∧ tangentAtPoint CD Q D ∧
  distinctPointsOnLine B A BA ∧ E.onLine BA ∧ between B A E ∧
  distinctPointsOnLine E C EC ∧ F.onLine EC ∧ F.onCircle P ∧
  distinctPointsOnLine E D ED ∧ G.onLine ED ∧ G.onCircle Q ∧
  distinctPointsOnLine F G FG ∧ H.onLine FG ∧
  distinctPointsOnLine A H AH ∧ (∠F:A:H = ∠H:A:G)
  → (∠F:C:H = ∠G:D:H) :=
by
  sorry

theorem problem_MP54 :
  ∀ (A B C D E M : Point) (AB BC CA AE : Line),
    (formTriangle A B C AB BC CA) ∧
    (threePointsOnLine B C D BC) ∧
    (threePointsOnLine B C E BC) ∧
    (between B C E) ∧
    (between C B D) ∧
    (∠ A:B:D = ∠ A:C:E + ∠ A:C:E) ∧
    (distinctPointsOnLine A E AE) ∧
    (perpLine AE BC) ∧
    (midpoint B M C)
    → (|(M─E)| + |(M─E)| = |(A─B)|) :=
by sorry

theorem problem_imo_2002_p2 :
∀ (B C O A E F D J : Point) (BC AC AD EF OJ : Line) (Γ : Circle),
  (B.onLine BC ∧ C.onLine BC ∧ O.onLine BC)
  ∧ (A.onLine AC ∧ C.onLine AC)
  ∧ (A.onLine AD ∧ D.onLine AD)
  ∧ (E.onLine EF ∧ F.onLine EF)
  ∧ (O.onLine OJ)
  ∧ O.isCentre Γ
  ∧ A.onCircle Γ
  ∧ B.onCircle Γ
  ∧ C.onCircle Γ
  ∧ E.onCircle Γ
  ∧ F.onCircle Γ
  ∧ D.onCircle Γ
  ∧ (∠ A:O:C > 60)
  ∧ perpBisector A O EF
  ∧ (∠ A:O:D = ∠ D:O:B)
  ∧ twoLinesIntersectAtPoint OJ AC J
  ∧ ¬(OJ.intersectsLine AD)
  → inCentre J C E F := by
sorry

theorem problem_97T18 :
∀ (A B C D E F P Q R M : Point)
  (AB BC CA AD BE CF EF DR : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C < ∟ ∧
  ∠B:C:A < ∟ ∧
  ∠C:A:B < ∟ ∧
  distinctPointsOnLine A D AD ∧
  D.onLine BC ∧
  perpLine AD BC ∧
  distinctPointsOnLine B E BE ∧
  E.onLine CA ∧
  perpLine BE CA ∧
  distinctPointsOnLine C F CF ∧
  F.onLine AB ∧
  perpLine CF AB ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint EF BC P ∧
  distinctPointsOnLine D R DR ∧
  D.onLine DR ∧
  ¬(DR.intersectsLine EF) ∧
  twoLinesIntersectAtPoint DR AC Q ∧
  twoLinesIntersectAtPoint DR AB R
  → midpoint B M C ∧
    cyclic P Q R M
:= by
  sorry

theorem problem_HP25 :
∀ (A B C O I J K D F G : Point)
  (AB BC CA AO DI FG : Line)
  (circleO circleI : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle circleO A B C ∧
  inCircle circleI AB BC CA ∧
  I.isCentre circleI ∧
  tangentAtPoint AB circleI J ∧
  tangentAtPoint AC circleI K ∧
  threePointsOnLine A O D AO ∧
  D.onCircle circleO ∧
  distinctPointsOnLine D I DI ∧
  threePointsOnLine C A F CA ∧
  |(A─F)| = |(B─J)| ∧
  perpLine FG DI ∧
  F.onLine FG ∧
  twoLinesIntersectAtPoint FG AB G
→ |(A─G)| = |(C─K)| :=
by sorry

theorem problem_HP2 :
  ∀ (A B C D E F M : Point) (AB BC AD EF CE DE : Line) (O : Circle),
    (A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O)
    ∧ C.sameSide D AB
    ∧ tangentAtPoint CE O C
    ∧ tangentAtPoint DE O D
    ∧ twoLinesIntersectAtPoint CE DE E
    ∧ twoLinesIntersectAtPoint AD BC F
    ∧ twoLinesIntersectAtPoint AB EF M
  → cyclic E C M D := by
  sorry

theorem problem_HP5 :
  ∀ (A B C D A' B' P Q : Point)
    (AC BD CA' DB' DB PQ : Line),
  (cyclic A B C D)
  ∧ (∠ B:A:D = ∟)
  ∧ (∠ B:C:D = ∟)
  ∧ perpBisector A A' BD
  ∧ perpBisector B B' AC
  ∧ distinctPointsOnLine A C AC
  ∧ distinctPointsOnLine C A' CA'
  ∧ distinctPointsOnLine D B DB
  ∧ distinctPointsOnLine D B' DB'
  ∧ distinctPointsOnLine P Q PQ
  ∧ twoLinesIntersectAtPoint AC DB' Q
  ∧ twoLinesIntersectAtPoint DB CA' P
  → perpLine PQ AC
:= by
  sorry

theorem problem_MP53 :
∀ (A B C D E F : Point)
  (AB BC CA AE CF BF FD : Line),
  formTriangle A B C AB BC CA ∧
  (∠ A:C:B = ∠ A:B:C + ∠ A:B:C) ∧
  D.onLine BC ∧
  E.onLine BC ∧
  F.onLine AE ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine C F CF ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine F D FD ∧
  perpLine CF AE ∧
  perpLine BF FD ∧
  (∠ D:F:E = ∠ A:B:C)
  → |(B─D)| = |(C─D)| + |(C─D)| :=
by sorry

theorem problem_HP87 :
∀ (A B C O H D E : Point) (AB BC CA CH OD DE : Line),
  (formTriangle A B C AB BC CA)
  ∧ circumCentre O A B C
  ∧ distinctPointsOnLine C H CH
  ∧ perpLine CH AB
  ∧ twoLinesIntersectAtPoint CH AB D
  ∧ distinctPointsOnLine O D OD
  ∧ distinctPointsOnLine D E DE
  ∧ perpLine DE OD
  ∧ twoLinesIntersectAtPoint DE CA E
  → ∠E:H:D = ∠B:A:C
:= by
  sorry

theorem problem_06G9 :
∀ (A B C A1 B1 C1 A2 B2 C2 A3 B3 C3 : Point)
  (AB BC CA : Line)
  (ω α β γ : Circle),
  (
    formTriangle A B C AB BC CA ∧
    threePointsOnLine B C A1 BC ∧
    threePointsOnLine C A B1 CA ∧
    threePointsOnLine A B C1 AB ∧
    circumCircle ω A B C ∧
    circumCircle α A B1 C1 ∧
    circumCircle β B C1 A1 ∧
    circumCircle γ C A1 B1 ∧
    A2.onCircle ω ∧ A2.onCircle α ∧
    B2.onCircle ω ∧ B2.onCircle β ∧
    C2.onCircle ω ∧ C2.onCircle γ ∧
    (∃ MBC : Point, midpoint B MBC C ∧ midpoint A1 A3 MBC) ∧
    (∃ MCA : Point, midpoint C MCA A ∧ midpoint B1 B3 MCA) ∧
    (∃ MAB : Point, midpoint A MAB B ∧ midpoint C1 C3 MAB)
  )
  →
  (∠ B2:A2:C2 = ∠ B3:A3:C3 ∧ ∠ A2:B2:C2 = ∠ A3:B3:C3)
:= by
  sorry

theorem problem_MP42 :
  ∀ (A B C P : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  ∠B:A:C = 100 ∧
  insideTriangle P A B C AB BC CA ∧
  ∠P:A:B = 25 ∧
  ∠P:B:A = 30
  → ∠A:C:P = 30
  := by
  sorry

theorem problem_imo_2019_p6 :
∀ (A B C I D E F P Q R X : Point)
  (AB BC CA DI EF DR AR AI AX PQ : Line)
  (w : Circle),
  formTriangle A B C AB BC CA ∧
  ¬(|(A─B)| = |(A─C)|) ∧
  inCentre I A B C ∧
  inCircle w AB BC CA ∧
  I.isCentre w ∧
  tangentAtPoint BC w D ∧
  tangentAtPoint CA w E ∧
  tangentAtPoint AB w F ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine D R DR ∧
  perpLine DR EF ∧
  R.onCircle w ∧
  distinctPointsOnLine A R AR ∧
  P.onLine AR ∧ P.onCircle w ∧ ¬(P = R) ∧
  cyclic P C E Q ∧
  cyclic P B F Q ∧
  distinctPointsOnLine D I DI ∧
  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine A I AI ∧
  distinctPointsOnLine A X AX ∧
  perpLine AI AX
  → twoLinesIntersectAtPoint DI PQ X ∧ X.onLine AX
:= by
  sorry

theorem HP58 :
∀ (A B C D E F G M N : Point) (P Q : Circle) (CD CE ED FG : Line),
  A.onCircle P ∧ B.onCircle P ∧ A.onCircle Q ∧ B.onCircle Q ∧
  C.onLine CD ∧ tangentAtPoint CD P C ∧ C.onCircle P ∧
  D.onLine CD ∧ tangentAtPoint CD Q D ∧ D.onCircle Q ∧
  between B A E ∧
  E.onLine CE ∧ C.onLine CE ∧ F.onLine CE ∧ F.onCircle P ∧
  E.onLine ED ∧ D.onLine ED ∧ G.onLine ED ∧ G.onCircle Q ∧
  F.onLine FG ∧ G.onLine FG ∧ M.onLine FG ∧ M.onCircle Q ∧ N.onLine FG ∧ N.onCircle P
→ ∠F:C:M = ∠G:D:N := by
  sorry

theorem problem_MP84 :
∀ (A B C D E F : Point) (AB BC CA AD BE : Line),
  formTriangle A B C AB BC CA ∧
  ∠ A:C:B = ∟ ∧
  |(A─B)| = |(A─C)| ∧
  threePointsOnLine B C D BC ∧
  |(C─D)| = ( |(B─C)| ) / 2 ∧
  midpoint A E C ∧
  twoLinesIntersectAtPoint BE AD F
  → ∠ A:F:E = ∟ / 2
  := by
sorry

theorem problem_MP21 : ∀
  (A B C D E : Point)
  (AB BC CA CD DE : Line),
  formTriangle A B C AB BC CA ∧
  ∠ A:C:B = ∟ ∧
  D.onLine AB ∧
  E.onLine BC ∧
  |(A─D)| = |(A─C)| ∧
  |(C─E)| = |(B─D)| + |(B─D)| ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D E DE ∧
  perpLine CD DE
  → |(A─C)| = |(B─C)|
:= by
  sorry

theorem problem_HP65 :
  ∀ (O A B C D E F G : Point) (Ω : Circle)
    (AB CD BC AE DF : Line),
  (O.isCentre Ω) ∧
  A.onCircle Ω ∧
  B.onCircle Ω ∧
  C.onCircle Ω ∧
  D.onCircle Ω ∧
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine D F DF ∧
  midpoint O A B ∧
  perpLine AB CD ∧
  midpoint O E C ∧
  F.onLine AE ∧
  F.onCircle Ω ∧
  twoLinesIntersectAtPoint DF BC G
  → midpoint B G C
:= by
  sorry

theorem problem_HP79 :
  ∀ (A B C D E F G H I : Point)
    (AB BC CA AD DE DF EF CG BG HI : Line),
    formTriangle A B C AB BC CA ∧
    twoLinesIntersectAtPoint BC AD D ∧
    (∠ B:A:D = ∠ D:A:C) ∧
    twoLinesIntersectAtPoint AB DE E ∧
    (∠ A:D:E = ∠ E:D:B) ∧
    twoLinesIntersectAtPoint AC DF F ∧
    (∠ A:D:F = ∠ F:D:C) ∧
    twoLinesIntersectAtPoint EF AD G ∧
    distinctPointsOnLine C G CG ∧
    twoLinesIntersectAtPoint CG DE H ∧
    distinctPointsOnLine B G BG ∧
    twoLinesIntersectAtPoint BG DF I ∧
    distinctPointsOnLine H I HI
  → A.onLine HI ∧ perpLine AD HI :=
by sorry

theorem problem_18G2 :
  ∀ (A B C M P X Y : Point) (AB BC CA PA PB PC : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(A─C)| ∧
    midpoint B M C ∧
    distinctPointsOnLine P A PA ∧
    distinctPointsOnLine B C BC ∧
    ¬(∃ Z : Point, twoLinesIntersectAtPoint PA BC Z) ∧
    |(P─B)| < |(P─C)| ∧
    distinctPointsOnLine P B PB ∧
    X.onLine PB ∧
    between P B X ∧
    distinctPointsOnLine P C PC ∧
    Y.onLine PC ∧
    between P C Y ∧
    ∠P:X:M = ∠P:Y:M
  → cyclic A P X Y
:= by sorry

theorem problem_11G5 :
∀ (A B C I D E F G P K : Point)
  (AB BC CA AI BI DE AC AE BD KP LA LB : Line)
  (ω : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  circumCircle ω A B C ∧
  distinctPointsOnLine A I AI ∧
  D.onLine AI ∧
  D.onCircle ω ∧
  distinctPointsOnLine B I BI ∧
  E.onLine BI ∧
  E.onCircle ω ∧
  distinctPointsOnLine D E DE ∧
  F.onLine DE ∧
  F.onLine AC ∧
  G.onLine DE ∧
  G.onLine BC ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine B D BD ∧
  tangentAtPoint LA ω A ∧
  tangentAtPoint LB ω B ∧
  twoLinesIntersectAtPoint LA LB K ∧
  distinctPointsOnLine K P KP
  →
  ((∃ (X : Point),
    X.onLine AE ∧
    X.onLine BD ∧
    X.onLine KP)
    ∨
    (¬(∃ (X : Point), X.onLine AE ∧ X.onLine BD)
     ∧ ¬(∃ (X : Point), X.onLine BD ∧ X.onLine KP)
     ∧ ¬(∃ (X : Point), X.onLine AE ∧ X.onLine KP))) :=
by
  sorry

theorem problem_MP88 :
  ∀ (A B C D E : Point) (AB BC CA CD DE : Line),
  (formTriangle A B C AB BC CA)
  ∧ (∠ A:C:B = ∟)
  ∧ (|(A─C)| + |(A─C)| + |(A─C)| + |(A─C)| = |(B─C)| + |(B─C)| + |(B─C)|)
  ∧ distinctPointsOnLine A B AB
  ∧ distinctPointsOnLine B C BC
  ∧ distinctPointsOnLine C A CA
  ∧ distinctPointsOnLine C D CD
  ∧ distinctPointsOnLine D E DE
  ∧ D.onLine AB
  ∧ E.onLine BC
  ∧ (|(A─D)| = |(A─C)|)
  ∧ (|(A─C)| = |(C─E)|)
  → perpLine CD DE :=
by
  sorry


theorem problem_HP37 :
∀ (A B C D E F H M N O : Point)
  (AB BC CA AD BE CF ED FD OB OC OH MN : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  distinctPointsOnLine A D AD ∧ D.onLine BC ∧ perpLine AD BC ∧
  distinctPointsOnLine B E BE ∧ E.onLine CA ∧ perpLine BE CA ∧
  distinctPointsOnLine C F CF ∧ F.onLine AB ∧ perpLine CF AB ∧
  twoLinesIntersectAtPoint AD BE H ∧ H.onLine CF ∧
  distinctPointsOnLine E D ED ∧ twoLinesIntersectAtPoint ED AB M ∧
  distinctPointsOnLine F D FD ∧ twoLinesIntersectAtPoint FD AC N ∧
  distinctPointsOnLine O B OB ∧
  distinctPointsOnLine O C OC ∧
  distinctPointsOnLine O H OH ∧
  distinctPointsOnLine M N MN
→ perpLine OB FD ∧ perpLine OC ED ∧ perpLine OH MN := by
  sorry

theorem problem_MP61 :
  ∀ (A B C D O E F : Point) (AB BC CD DA AC BD : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    twoLinesIntersectAtPoint AC BD O ∧
    midpoint B E C ∧
    midpoint A F D
  → midpoint E O F := by
  sorry

theorem problem_MP85 :
  ∀ (A B C D E F P : Point) (AB BC CA AP CD EF : Line),
    formTriangle A B C AB BC CA ∧
    D.onLine AB ∧
    (∠A:C:D = ∠A:B:C) ∧
    midpoint C P D ∧
    distinctPointsOnLine A P AP ∧
    twoLinesIntersectAtPoint AP BC E ∧
    distinctPointsOnLine C D CD ∧
    distinctPointsOnLine E F EF ∧
    F.onLine AB ∧
    ¬(EF.intersectsLine CD)
    → (|(E─F)| * |(E─F)| = |(C─E)| * |(B─E)|) := by
  sorry

theorem problem_HP43 :
  ∀ (A B C D E P : Point) (AB BC CA AE PD : Line),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine P D PD ∧
  D.onLine BC ∧
  E.onLine BC ∧
  |(B─D)| = |(C─E)| ∧
  insideTriangle P A B C AB BC CA ∧
  ¬(PD.intersectsLine AE) ∧
  ∠ P:A:B = ∠ E:A:C
  → ∠ P:B:A = ∠ P:C:A
:= by
  sorry

theorem problem_MP48 :
  ∀ (A B C D E F : Point) (AB BC CA BD DA CE EA : Line),
  formTriangle A B C AB BC CA ∧
  formTriangle A B D AB BD DA ∧
  ∠A:D:B = ∟ ∧
  ∠A:B:D = 30 ∧
  formTriangle A C E AC CE EA ∧
  ∠A:E:C = ∟ ∧
  ∠A:C:E = 30 ∧
  midpoint B F C
  → ( |(D─E)| = |(E─F)| ) ∧ ( |(E─F)| = |(F─D)| ) :=
by
  sorry

theorem problem_HP52 :
∀ (A B C D E F O : Point)
  (AB AC AO DC DE : Line)
  (Ω P Q : Circle),
  O.isCentre Ω ∧
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧
  A.onLine AB ∧ B.onLine AB ∧
  A.onLine AC ∧ C.onLine AC ∧
  C.onLine DC ∧ D.onLine DC ∧
  perpLine DC AC ∧
  twoLinesIntersectAtPoint AB DC D ∧
  A.onLine AO ∧ O.onLine AO ∧
  D.onLine DE ∧ E.onLine DE ∧
  perpLine DE AO ∧
  twoLinesIntersectAtPoint DE AC E ∧
  E.onLine AC ∧
  F.onLine DE ∧ F.onCircle Ω ∧
  circumCircle P B E F ∧
  circumCircle Q C D F
  → ∀ (X : Point),
    X.onCircle P ∧ X.onCircle Q → X = F
:= by
  sorry

theorem problem_11G7 :
∀ (A B C D E F O J K L : Point)
  (AB BC CD DE EF FA OE DF BJ BK KL : Line)
  (incC : Circle),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine B C BC ∧
  distinctPointsOnLine C D CD ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine E F EF ∧
  distinctPointsOnLine F A FA ∧
  tangentLine AB incC ∧
  tangentLine BC incC ∧
  tangentLine CD incC ∧
  tangentLine DE incC ∧
  tangentLine EF incC ∧
  tangentLine FA incC ∧
  circumCentre O A C E ∧
  distinctPointsOnLine B J BJ ∧
  twoLinesIntersectAtPoint CD BJ J ∧
  perpLine BJ CD ∧
  distinctPointsOnLine D F DF ∧
  distinctPointsOnLine O E OE ∧
  distinctPointsOnLine B K BK ∧
  twoLinesIntersectAtPoint BK OE K ∧
  perpLine BK DF ∧
  distinctPointsOnLine K L KL ∧
  twoLinesIntersectAtPoint KL DE L ∧
  perpLine KL DE
  → |(D─J)| = |(D─L)| :=
by
  sorry

theorem problem_MP65 :
∀ (A B C D E F P : Point) (AB BC CA AP : Line),
  (formTriangle A B C AB BC CA) ∧
  (|(A─B)| = |(A─C)|) ∧
  E.onLine AB ∧
  F.onLine CA ∧
  midpoint E P F ∧
  distinctPointsOnLine A P AP ∧
  twoLinesIntersectAtPoint AP BC D
  →
  ((|(D─E)| * |(D─E)|) - (|(B─E)| * |(B─E)|) = (|(D─F)| * |(D─F)|) - (|(C─F)| * |(C─F)|))
:= by
  sorry

theorem problem_HP51 :
  ∀ (A B C D E F G : Point)
    (AB BC CA DA CF EF FG : Line)
    (O : Circle),
    formTriangle A B C AB BC CA ∧
    circumCircle O A B C ∧
    D.onCircle O ∧
    E.onCircle O ∧
    twoLinesIntersectAtPoint AB CF F ∧
    perpLine CF AB ∧
    distinctPointsOnLine E F EF ∧
    perpLine FG EF ∧
    twoLinesIntersectAtPoint DA FG G
  → |(C─G)| = |(C─D)| :=
by sorry

theorem problem_HP68 :
  ∀ (A B C D E F G H K : Point)
    (AB BC CA CH EF GK CD : Line)
    (O P : Circle),
    (formTriangle A B C AB BC CA)
  ∧ (circumCircle O A B C)
  ∧ (¬(|(A─C)| = |(B─C)|))
  ∧ distinctPointsOnLine C H CH
  ∧ (∠ A:C:H = ∠ H:C:B)
  ∧ H.onCircle O
  ∧ E.onLine CA
  ∧ F.onLine CB
  ∧ between A E C
  ∧ between B F C
  ∧ distinctPointsOnLine E F EF
  ∧ (¬(EF.intersectsLine AB))
  ∧ twoLinesIntersectAtPoint EF CH K
  ∧ circumCircle P E F H
  ∧ G.onCircle O
  ∧ G.onCircle P
  ∧ distinctPointsOnLine G K GK
  ∧ D.onLine GK
  ∧ D.onCircle O
  ∧ distinctPointsOnLine C D CD
  → (¬(CD.intersectsLine AB)) :=
by
  sorry

theorem problem_11G6 :
  ∀ (A B C D E F I K : Point) (AB BC CA BD AE BE AF CI : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| = |(A─C)|)
  ∧ (midpoint A D C)
  ∧ (distinctPointsOnLine A E AE)
  ∧ (cyclic A B C E)
  ∧ (∠ B:A:E = ∠ E:A:C)
  ∧ (distinctPointsOnLine B D BD)
  ∧ (distinctPointsOnLine B F BD)
  ∧ (cyclic A E B F)
  ∧ (twoLinesIntersectAtPoint AF BE I)
  ∧ (twoLinesIntersectAtPoint CI BD K)
  → inCentre I A B K := by
  sorry

theorem problem_HP69 :
∀ (A B C D E F O P : Point) (Om Pm : Circle) (AB CD EF : Line),
  O.isCentre Om ∧ P.isCentre Pm
  ∧ A.onCircle Om ∧ B.onCircle Om ∧ A.onCircle Pm ∧ B.onCircle Pm
  ∧ C.onCircle Pm ∧ D.onCircle Pm ∧ O.onLine CD ∧ distinctPointsOnLine C D CD
  ∧ E.onCircle Om ∧ F.onCircle Om ∧ P.onLine EF ∧ distinctPointsOnLine E F EF
  ∧ cyclic C E D F
→
  ( (∀ (M : Circle),
      (C.onCircle M ∧ E.onCircle M ∧ D.onCircle M ∧ F.onCircle M)
      → ∃ (X : Point), X.isCentre M ∧ X.onLine AB)
    ∧
    (∃ (G : Point), twoLinesIntersectAtPoint AB CD G ∧ G.onLine EF) )
:= by
  sorry

theorem problem_MP62 :
∀ (A B C M D E F P : Point)
  (AB BC CA AD ME BE AP : Line),
  (formTriangle A B C AB BC CA)
  ∧ (|(A─B)| > |(A─C)|)
  ∧ midpoint B M C
  ∧ twoLinesIntersectAtPoint AD BC D
  ∧ perpLine AD BC
  ∧ twoLinesIntersectAtPoint ME AC E
  ∧ perpLine ME AC
  ∧ twoLinesIntersectAtPoint AD ME F
  ∧ midpoint E F F
  → perpLine AP BE := by
sorry

theorem problem_MP86 :
∀ (A B C D E F : Point) (AB : Line),
  threePointsOnLine A B C AB ∧
  between A C B ∧
  threePointsOnLine A B D AB ∧
  between A D B ∧
  |(A─C)| = |(B─D)| ∧
  E.sameSide F AB ∧
  (∠ E:A:B = ∠ A:B:E) ∧
  (∠ A:B:E = ∠ E:C:F)
→ ∠ E:D:F = ∠ E:C:F := by
  sorry

theorem problem_imo_2017_p4 :
  ∀ (R S T J A K : Point) (ℓ AJ TK : Line) (Ω Γ : Circle),
  ( R ≠ S ∧
    R.onCircle Ω ∧
    S.onCircle Ω ∧
    (∀ O : Point, O.isCentre Ω → ∠ R:O:S ≠ ∟ + ∟) ∧
    tangentAtPoint ℓ Ω R ∧
    midpoint R S T ∧
    J.onCircle Ω ∧
    circumCircle Γ J S T ∧
    A.onLine ℓ ∧
    A.onCircle Γ ∧
    threePointsOnLine A J K AJ ∧
    K.onCircle Ω ∧
    distinctPointsOnLine K T TK
  )
  → tangentLine TK Γ := by
  sorry

theorem problem_13G5 :
  ∀ (A B C D E F : Point) (AB BC CD DE EF FA AD BE CF : Line),
  |(A─B)|=|(D─E)| ∧
  |(B─C)|=|(E─F)| ∧
  |(C─D)|=|(F─A)| ∧
  ( (∠F:A:B) - (∠C:D:E) = (∠B:C:D) - (∠E:F:A) ) ∧
  ( (∠B:C:D) - (∠E:F:A) = (∠D:E:F) - (∠A:B:C) )
  → ∃ (X : Point), twoLinesIntersectAtPoint AD BE X ∧ X.onLine CF :=
by
  sorry

theorem problem_MP8 :
∀ (A B C D : Point) (AB BC CA AD : Line),
  formTriangle A B C AB BC CA ∧
  (∠A:C:B = ∠B:A:C + ∠A:B:C + ∠A:B:C) ∧
  twoLinesIntersectAtPoint AD BC D ∧
  perpLine AD BC
→ |(A─B)| = (|(B─C)| + |(C─D)| + |(C─D)|) :=
by sorry

theorem problem_17G4 :
∀ (A B C D E F P Q M : Point) (AB BC CA : Line) (ω α : Circle),
  (formTriangle A B C AB BC CA)
  ∧ tangentAtPoint BC ω D
  ∧ tangentAtPoint CA ω E
  ∧ tangentAtPoint AB ω F
  ∧ circumCircle α A E F
  ∧ P.onLine BC ∧ P.onCircle α
  ∧ Q.onLine BC ∧ Q.onCircle α
  ∧ midpoint A M D
→ ∀ (Γ : Circle),
     (circumCircle Γ M P Q
      → ∀ (X Y : Point),
           (X.onCircle Γ ∧ X.onCircle ω ∧ Y.onCircle Γ ∧ Y.onCircle ω)
           → X = Y) :=
by sorry

theorem problem_imo_2021_p3 :
∀ (A B C D E F X O₁ O₂ : Point)
  (AB BC CA EF O₁O₂ : Line),
  formTriangle A B C AB BC CA ∧
  insideTriangle D A B C AB BC CA ∧
  ∠ D:A:B = ∠ C:A:D ∧
  E.onLine CA ∧ between A E C ∧
  ∠ A:D:E = ∠ B:C:D ∧
  F.onLine AB ∧ between A F B ∧
  ∠ F:D:A = ∠ D:B:C ∧
  X.onLine CA ∧
  |(C─X)| = |(B─X)| ∧
  circumCentre O₁ A D C ∧
  circumCentre O₂ E X D ∧
  B.onLine BC ∧ C.onLine BC ∧
  E.onLine EF ∧ F.onLine EF ∧
  O₁.onLine O₁O₂ ∧ O₂.onLine O₁O₂
  → ∃ P : Point, P.onLine BC ∧ P.onLine EF ∧ P.onLine O₁O₂ :=
by
  sorry

theorem problem_MP44 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:C:B > ∟ ∧
  D.onLine BC ∧
  E.onLine BC ∧
  ∠B:A:D = ∠D:A:C ∧
  ∠B:A:E = ∠E:A:C ∧
  (|(A─B)| + |(A─B)| = |(B─D)| + |(B─E)|)
  → ∠A:C:B = ∟ + (1/2)*∠A:B:C
:= by
  sorry

theorem problem_HP22 :
∀
(A B C D E F G P : Point)
(L1 L2 L3 L4 L5 L6 L7 : Line)
(O : Circle),
(
  C.onCircle O ∧ D.onCircle O ∧ E.onCircle O ∧ A.onCircle O ∧ B.onCircle O
  ∧ distinctPointsOnLine P C L1 ∧ tangentAtPoint L1 O C
  ∧ distinctPointsOnLine P E L2 ∧ tangentAtPoint L2 O E
  ∧ threePointsOnLine P B A L3
  ∧ distinctPointsOnLine A C L4 ∧ distinctPointsOnLine B D L5 ∧ twoLinesIntersectAtPoint L4 L5 F
  ∧ distinctPointsOnLine D E L6 ∧ distinctPointsOnLine A B L7 ∧ twoLinesIntersectAtPoint L6 L7 G
)
→ ∠ G:F:E = ∠ A:D:E
:= by
  sorry

theorem problem_HP16 :
∀ (A B C D E F G : Point) (O : Circle)
  (AB BC CA AD EF CG : Line),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  midpoint B D C ∧
  threePointsOnLine A D E AD ∧
  E.onCircle O ∧
  distinctPointsOnLine E F EF ∧
  F.onCircle O ∧
  ¬(EF.intersectsLine BC) ∧
  distinctPointsOnLine C G CG ∧
  twoLinesIntersectAtPoint AD CG G ∧
  perpLine CG CA
→ ∠A:G:C = ∠F:G:C
:= by
  sorry

theorem problem_HP70 :
  ∀ (A B C D E F G J K M N : Point)
    (AB BC CA JK MN GD : Line)
    (CE CF : Circle),
  (formTriangle A B C AB BC CA)
  ∧ D.onLine BC
  ∧ inCentre E A B D
  ∧ inCentre F A C D
  ∧ E.isCentre CE
  ∧ D.onCircle CE
  ∧ F.isCentre CF
  ∧ D.onCircle CF
  ∧ G.onCircle CE
  ∧ G.onCircle CF
  ∧ J.onLine AB
  ∧ J.onCircle CE
  ∧ K.onLine BC
  ∧ K.onCircle CE
  ∧ M.onLine AC
  ∧ M.onCircle CF
  ∧ N.onLine BC
  ∧ N.onCircle CF
  ∧ distinctPointsOnLine J K JK
  ∧ distinctPointsOnLine M N MN
  ∧ distinctPointsOnLine G D GD
  → ∃ X : Point, twoLinesIntersectAtPoint JK MN X ∧ X.onLine GD
:= by
  sorry

theorem problem_MP11 :
  ∀ (A B C D : Point) (AB BC CD DA AC : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    distinctPointsOnLine A C AC ∧
    (∠A:B:C = ∠C:D:A + ∠C:D:A) ∧
    (∠B:C:A = ∠A:C:D)
  → (|(A─B)| + |(B─C)| = |(C─D)|)
  := by
  sorry

theorem problem_16G2 :
  ∀ (A B C I M D E F X Y : Point)
    (AB BC CA AI AM XD EF ID : Line)
    (Ω1 Ω2 : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  midpoint B M C ∧
  D.onLine BC ∧
  distinctPointsOnLine I D ID ∧
  perpLine BC ID ∧
  distinctPointsOnLine A I AI ∧
  perpLine EF AI ∧
  I.onLine EF ∧
  E.onLine EF ∧
  F.onLine EF ∧
  F.onLine AB ∧
  E.onLine CA ∧
  distinctPointsOnLine A M AM ∧
  distinctPointsOnLine X D XD ∧
  circumCircle Ω1 A E F ∧
  circumCircle Ω2 A B C ∧
  X.onCircle Ω1 ∧
  X.onCircle Ω2 ∧
  X ≠ A ∧
  twoLinesIntersectAtPoint XD AM Y
  → Y.onCircle Ω2 := by
  sorry

theorem problem_HP63 :
∀ (A B C D E F O : Point)
  (AB CA DB CD EC ED OF EF : Line)
  (Ω : Circle),
  distinctPointsOnLine A B AB ∧
  O.isCentre Ω ∧
  A.onCircle Ω ∧
  B.onCircle Ω ∧
  twoLinesIntersectAtPoint AB CA A ∧
  perpLine AB CA ∧
  twoLinesIntersectAtPoint AB DB B ∧
  perpLine AB DB ∧
  tangentLine EC Ω ∧
  tangentLine ED Ω ∧
  distinctPointsOnLine C D CD ∧
  twoLinesIntersectAtPoint OF CD F ∧
  perpLine OF CD ∧
  distinctPointsOnLine E F EF
  → ∠ E:F:D = ∠ F:O:B :=
by
  sorry

theorem HP86 :
∀ (A B C D E F H : Point) (AB BC CA DH EF DE DF : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  midpoint B D C ∧
  distinctPointsOnLine D H DH ∧
  distinctPointsOnLine E F EF ∧
  E.onLine AB ∧
  F.onLine AC ∧
  perpLine DH EF ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine D F DF
  → |(D─E)| = |(D─F)| := by
sorry

theorem problem_MP90 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C = ∟) ∧
  (4 * |(A─B)| = 3 * |(A─C)|) ∧
  D.onLine CA ∧
  (4 * |(A─D)| = |(A─C)|) ∧
  E.onLine AB ∧
  (∠A:E:D = ∠D:B:C)
  → 8 * |(A─E)| = |(E─B)| := by
  sorry

theorem problem_17G5 :
  ∀ (A B C A_1 B_1 C_1 D E F : Point)
    (AC_1 A_1C BB_1 DE L : Line)
    (Ω1 Ω2 : Circle),
  (|(A─B)| = |(B─C)|)
  ∧ perpBisector A A_1 L
  ∧ perpBisector B B_1 L
  ∧ perpBisector C C_1 L
  ∧ distinctPointsOnLine A C_1 AC_1
  ∧ distinctPointsOnLine A_1 C A_1C
  ∧ twoLinesIntersectAtPoint AC_1 A_1C D
  ∧ circumCircle Ω1 A B C
  ∧ circumCircle Ω2 A_1 B C_1
  ∧ E.onCircle Ω1
  ∧ E.onCircle Ω2
  ∧ E ≠ B
  ∧ distinctPointsOnLine B B_1 BB_1
  ∧ distinctPointsOnLine D E DE
  ∧ twoLinesIntersectAtPoint BB_1 DE F
  → F.onCircle Ω1 := by
  sorry

theorem problem_MP2 :
  ∀ (A B C D E F : Point) (AB BC CA EF : Line),
    formTriangle A B C AB BC CA ∧
    insideTriangle D A B C AB BC CA ∧
    (|(D─B)| = |(D─C)|) ∧
    (∠ A:D:E = ∠ E:D:B) ∧
    (∠ B:E:D = ∟) ∧
    (∠ A:D:F = ∠ F:D:C) ∧
    (∠ C:F:D = ∟) ∧
    distinctPointsOnLine E F EF
  → ¬(∃ (X : Point), twoLinesIntersectAtPoint EF BC X) :=
by sorry

theorem problem_MP32 : ∀
  (A B C D E : Point)
  (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠B:A:C = ∟) ∧
  (∠A:B:C = 75) ∧
  midpoint B D C ∧
  E.onLine CA ∧
  (|(A─E)| = |(A─B)|)
  → (∠B:D:E = 45)
:= by
  sorry

theorem problem_17G3 :
∀ (A B C O H M P Q O₁ : Point)
  (AB BC CA OA AM altB altC : Line),
  formTriangle A B C AB BC CA ∧
  ¬(|(A─B)| = |(A─C)|) ∧
  ¬(|(B─C)| = |(A─B)|) ∧
  ¬(|(B─C)| = |(A─C)|) ∧
  circumCentre O A B C ∧
  B.onLine altB ∧ perpLine altB CA ∧
  C.onLine altC ∧ perpLine altC AB ∧
  twoLinesIntersectAtPoint altB altC H ∧
  midpoint B M C ∧
  distinctPointsOnLine O A OA ∧
  twoLinesIntersectAtPoint OA altB P ∧
  twoLinesIntersectAtPoint OA altC Q ∧
  circumCentre O₁ P Q H ∧
  distinctPointsOnLine A M AM
  → O₁.onLine AM :=
by
  sorry

theorem problem_HP3 :
  ∀ (A B C D E F P : Point) (AB PB AF BE PE PF : Line) (ω : Circle),
    distinctPointsOnLine A B AB ∧
    A.onCircle ω ∧
    B.onCircle ω ∧
    distinctPointsOnLine P E PE ∧
    tangentAtPoint PE ω E ∧
    distinctPointsOnLine P F PF ∧
    tangentAtPoint PF ω F ∧
    threePointsOnLine P B C PB ∧
    C.onCircle ω ∧
    distinctPointsOnLine A F AF ∧
    distinctPointsOnLine B E BE ∧
    twoLinesIntersectAtPoint AF BE D
  → ∠D:P:E = ∠A:C:D + ∠A:C:D := by
  sorry

theorem problem_HP33 :
∀ (A B P C D : Point) (O₁ O₂ : Circle) (PCLine PDLine : Line) (r₁ r₂ : ℝ),
A.onCircle O₁ ∧ B.onCircle O₁ ∧ A.onCircle O₂ ∧ B.onCircle O₂ ∧
distinctPointsOnLine P C PCLine ∧ tangentAtPoint PCLine O₁ C ∧
distinctPointsOnLine P D PDLine ∧ tangentAtPoint PDLine O₂ D ∧
(|(P─C)| / |(P─D)|) = (r₁ / r₂)
→
(∠P:C:A = ∠P:B:D) ∧ (∠C:A:P = ∠B:D:P) ∧ (∠A:P:C = ∠D:P:B)
:= by
  sorry

theorem problem_05G6 :
∀ (A B C M K L X Y P Q : Point)
  (AB BC CA AM AX AY : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  inCircle Ω AB BC CA ∧
  midpoint B M C ∧
  distinctPointsOnLine A M AM ∧
  K.onLine AM ∧ K.onCircle Ω ∧
  L.onLine AM ∧ L.onCircle Ω ∧
  distinctPointsOnLine A X AX ∧
  X.onCircle Ω ∧
  twoLinesIntersectAtPoint AX BC P ∧
  distinctPointsOnLine A Y AY ∧
  Y.onCircle Ω ∧
  twoLinesIntersectAtPoint AY BC Q
→ |(B─P)| = |(C─Q)| :=
by sorry

theorem problem_MP68 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠ A:B:C = 60 ∧
    ∠ B:C:A = 70 ∧
    between A D C ∧
    between A E B ∧
    ∠ D:B:C = 40 ∧
    ∠ E:C:B = 40
  → ∠ B:D:E = 30 :=
by
  sorry


theorem HP21 :
∀ (A B C D E F G M O : Point)
  (AB BC CA AD BF DE AO CM : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  between B D C ∧
  ∠ D:A:C = ∠ A:B:D ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine B F BF ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine A O AO ∧
  distinctPointsOnLine C M CM ∧
  B.onCircle Ω ∧ D.onCircle Ω ∧ E.onCircle Ω ∧ F.onCircle Ω ∧
  O.isCentre Ω ∧
  E.onLine AB ∧
  F.onLine AD ∧
  twoLinesIntersectAtPoint BF DE G ∧
  midpoint A M G
→ perpLine AO CM
:= by
  sorry

theorem problem_13G2 :
∀ (A B C T M N X Y K : Point)
  (AB BC CA MN XY L1 L2 : Line)
  (Γ Ω1 Ω2 : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  T.onCircle Γ ∧ |(T─B)| = |(T─C)| ∧
  midpoint A M B ∧
  midpoint A N C ∧
  distinctPointsOnLine M N MN ∧
  distinctPointsOnLine X Y XY ∧
  circumCircle Ω1 A M T ∧
  circumCircle Ω2 A N T ∧
  perpBisector A C L1 ∧
  perpBisector A B L2 ∧
  X.onLine L1 ∧ X.onCircle Ω1 ∧
  Y.onLine L2 ∧ Y.onCircle Ω2 ∧
  twoLinesIntersectAtPoint MN XY K
  → |(K─A)| = |(K─T)| :=
by sorry

theorem problem_MP27 :
  ∀ (A B C D E F : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| = |(B─C)| ∧
    |(B─C)| = |(C─D)| ∧
    |(C─D)| = |(D─A)| ∧
    midpoint A E D ∧
    F.onLine DA ∧
    |(B─F)| = |(C─D)| + |(D─F)|
    → ∠ A:B:E + ∠ A:B:E = ∠ F:B:C := by
  sorry

theorem problem_HP84 :
∀ (A B C D E F S T : Point) (AB BC CD DA FE : Line) (O₁ O₂ O₃ O₄ : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  between A E D ∧
  between B F C ∧
  (|(A─E)| * |(F─C)| = |(B─F)| * |(E─D)|) ∧
  distinctPointsOnLine F E FE ∧
  twoLinesIntersectAtPoint FE AB S ∧
  twoLinesIntersectAtPoint FE CD T ∧
  circumCircle O₁ S A E ∧
  circumCircle O₂ S B F ∧
  circumCircle O₃ T D E ∧
  circumCircle O₄ T C F
→ True :=
by
  sorry

theorem problem_MP100 :
  ∀ (A B C D P E G F : Point) (AB BC CA AD CD PE PF : Line),
    formTriangle A B C AB BC CA ∧
    midpoint B D C ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine C D CD ∧
    P.onLine CD ∧
    distinctPointsOnLine P E PE ∧
    ¬(PE.intersectsLine AC) ∧
    twoLinesIntersectAtPoint PE AB E ∧
    twoLinesIntersectAtPoint PE AD G ∧
    distinctPointsOnLine P F PF ∧
    ¬(PF.intersectsLine AB) ∧
    twoLinesIntersectAtPoint PF CA F
  → |(E─G)| = |(C─F)| :=
by
  sorry

theorem problem_MP15 : ∀
  (A B C D E F : Point)
  (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠A:C:B = ∟) ∧
  (∠B:A:C = ∟/3) ∧
  E.onLine AB ∧
  (∠A:C:E = ∠E:C:B) ∧
  F.onLine BC ∧
  (∠B:A:F = ∠F:A:C) ∧
  D.onLine CA ∧
  (|(C─D)| = |(C─F)|)
  → ∠C:E:D = ∟/6
:= by
  sorry

theorem problem_MP89 :
  ∀ (A B C D E : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    ∠B:A:C = ∟ ∧
    |(A─B)| = |(A─C)| ∧
    midpoint A D C ∧
    E.onLine AB ∧
    ∠A:D:E = ∠D:B:C
    → 5 * |(A─E)| = |(E─B)| := by
  sorry

theorem problem_HP73 :
∀ (A B C H E F K G D : Point) (O P : Circle)
  (AC BC AB EF CH GK CD : Line),
  (formTriangle A B C AB BC AC) ∧
  (AC ≠ BC) ∧
  (circumCircle O A B C) ∧
  E.onLine AC ∧
  F.onLine BC ∧
  (∀ X : Point, ¬(twoLinesIntersectAtPoint EF AB X)) ∧
  twoLinesIntersectAtPoint EF CH K ∧
  (∠ A:C:H = ∠ H:C:B) ∧
  H.onLine CH ∧
  H.onCircle O ∧
  circumCircle P E F H ∧
  G.onCircle O ∧
  G.onCircle P ∧
  D.onLine GK ∧
  D.onCircle O ∧
  distinctPointsOnLine C D CD
→ ∀ X : Point, ¬(twoLinesIntersectAtPoint CD AB X)
:= by
  sorry

theorem problem_HP44 :
  ∀ (A B C O P D E F : Point)
    (AB AC BC OC PD PE : Line)
    (O₀ : Circle),
    O.isCentre O₀ ∧
    A.onCircle O₀ ∧
    B.onCircle O₀ ∧
    C.onCircle O₀ ∧
    distinctPointsOnLine A B AB ∧
    O.onLine AB ∧
    distinctPointsOnLine O C OC ∧
    perpLine AB OC ∧
    P.onLine AB ∧
    distinctPointsOnLine P D PD ∧
    tangentAtPoint PD O₀ D ∧
    distinctPointsOnLine P E PE ∧
    ∠D:P:E = ∠E:P:B ∧
    distinctPointsOnLine A C AC ∧
    twoLinesIntersectAtPoint AC PE E ∧
    distinctPointsOnLine B C BC ∧
    twoLinesIntersectAtPoint BC PE F
  → ∠E:O:F = ∟ :=
by sorry

theorem problem_HP42 :
∀ (A B C H D E F : Point) (AB BC CA DH EF : Line),
  formTriangle A B C AB BC CA ∧
  -- “H is the orthocenter of triangle ABC” (no built-in predicate available, treated as given) ∧
  midpoint B D C ∧
  distinctPointsOnLine D H DH ∧
  perpLine EF DH ∧
  E.onLine AB ∧
  F.onLine AC ∧
  E.onLine EF ∧
  F.onLine EF
→ midpoint E H F
:= by
  sorry

theorem problem_18G4 :
∀ (A B C T A_1 B_1 C_1 A_2 B_2 C_2 : Point)
  (AB BC CA A_1T B_1T C_1T AA2 BB2 CC2 : Line)
  (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  insideTriangle T A B C AB BC CA ∧
  perpBisector T A_1 BC ∧
  perpBisector T B_1 CA ∧
  perpBisector T C_1 AB ∧
  circumCircle Γ A_1 B_1 C_1 ∧
  distinctPointsOnLine A_1 T A_1T ∧
  distinctPointsOnLine B_1 T B_1T ∧
  distinctPointsOnLine C_1 T C_1T ∧
  A_2.onLine A_1T ∧
  A_2.onCircle Γ ∧
  B_2.onLine B_1T ∧
  B_2.onCircle Γ ∧
  C_2.onLine C_1T ∧
  C_2.onCircle Γ ∧
  distinctPointsOnLine A A_2 AA2 ∧
  distinctPointsOnLine B B_2 BB2 ∧
  distinctPointsOnLine C C_2 CC2
→ ∃ (X : Point),
    X.onLine AA2 ∧ X.onLine BB2 ∧ X.onLine CC2 ∧ X.onCircle Γ
:= by
  sorry

theorem problem_HP77 :
∀ (A B C D E P M N : Point)
  (AB BC CD DE EA BD CE BE MN AP : Line),
  formPentagon A B C D E AB BC CD DE EA
  ∧ (¬ (∃ X : Point, twoLinesIntersectAtPoint AB DE X))
  ∧ (¬ (∃ X : Point, twoLinesIntersectAtPoint AE BC X))
  ∧ twoLinesIntersectAtPoint BD CE P
  ∧ midpoint B M E
  ∧ midpoint C N D
  → ¬ (∃ X : Point, twoLinesIntersectAtPoint MN AP X) := by
sorry

theorem problem_HP83 :
  ∀ (A B C L E F O : Point) (Ω : Circle)
    (AB BC CA EL CL FL BL L_OF : Line),
  formTriangle A B C AB BC CA ∧
  O.isCentre Ω ∧
  A.onCircle Ω ∧
  B.onCircle Ω ∧
  C.onCircle Ω ∧
  L.onCircle Ω ∧
  distinctPointsOnLine E L EL ∧
  distinctPointsOnLine C L CL ∧
  perpLine EL CL ∧
  twoLinesIntersectAtPoint EL AB E ∧
  distinctPointsOnLine F L FL ∧
  distinctPointsOnLine B L BL ∧
  perpLine FL BL ∧
  twoLinesIntersectAtPoint FL CA F
  → threePointsOnLine E O F L_OF
:= by
  sorry

theorem problem_HP100 :
  ∀ (A D E B C O G P : Point)
    (AD DE EA BD AC OG : Line)
    (ω Ω : Circle),
    formTriangle A D E AD DE EA ∧
    O.isCentre ω ∧
    D.onCircle ω ∧
    B.onCircle ω ∧
    C.onCircle ω ∧
    B.onLine AE ∧
    C.onLine DE ∧
    twoLinesIntersectAtPoint BD AC G ∧
    circumCircle Ω A D E ∧
    O.onLine OG ∧
    G.onLine OG ∧
    P.onLine OG ∧
    P.onCircle Ω
  → ∃ (I : Point),
      inCentre I P B D ∧ inCentre I P A C
:= by
  sorry

theorem problem_16G5 :
∀ (A B C D H M X Y O : Point)
  (AB BC CA L AD AH : Line)
  (S : Circle),
  formTriangle A B C AB BC CA ∧
  D.onLine L ∧ distinctPointsOnLine A D AD ∧ perpLine AD L ∧
  H.onLine BC ∧ distinctPointsOnLine A H AH ∧ perpLine AH BC ∧
  midpoint B M C ∧
  A.onCircle S ∧ D.onCircle S ∧ X.onLine AB ∧ X.onCircle S ∧ Y.onLine AC ∧ Y.onCircle S ∧
  circumCentre O X A Y
  → |(O─H)| = |(O─M)| :=
by sorry

theorem problem_18G7 :
∀ (A B C O P O_A O_B O_C X_A X_B X_C : Point)
  (AB BC CA OP l_A l_B l_C : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  O.isCentre Ω ∧
  circumCircle Ω A B C ∧
  P.onCircle Ω ∧
  circumCentre O_A A O P ∧
  circumCentre O_B B O P ∧
  circumCentre O_C C O P ∧
  O_A.onLine l_A ∧ perpLine l_A BC ∧
  O_B.onLine l_B ∧ perpLine l_B CA ∧
  O_C.onLine l_C ∧ perpLine l_C AB ∧
  twoLinesIntersectAtPoint OP l_A X_A ∧
  twoLinesIntersectAtPoint OP l_B X_B ∧
  twoLinesIntersectAtPoint OP l_C X_C
  → True
  -- The circumcircle of triangle X_A X_B X_C is tangent to the circle Ω
  -- (No direct predicate is available for “circle tangent to circle,” so the conclusion is stated textually.)
  :=
by sorry

theorem problem_imo_2015_p4 :
∀
(A B C O D E F G K L X : Point)
(AB BC CA BD DF FB CG GE EC AO FK GL : Line)
(circle_BDF circle_CGE Γ Ω : Circle),
  (formTriangle A B C AB BC CA) ∧
  (circumCentre O A B C) ∧
  (circumCircle Ω A B C) ∧
  (A.isCentre Γ) ∧
  (D.onLine BC) ∧ (E.onLine BC) ∧
  (D.onCircle Γ) ∧ (E.onCircle Γ) ∧
  (between B D C) ∧ (between D E C) ∧
  (F.onCircle Γ) ∧ (F.onCircle Ω) ∧
  (G.onCircle Γ) ∧ (G.onCircle Ω) ∧
  (formTriangle B D F BD DF FB) ∧
  (circumCircle circle_BDF B D F) ∧
  (K.onLine AB) ∧ (K.onCircle circle_BDF) ∧ (between A K B) ∧
  (formTriangle C G E CG GE EC) ∧
  (circumCircle circle_CGE C G E) ∧
  (L.onLine CA) ∧ (L.onCircle circle_CGE) ∧ (between C L A) ∧
  (distinctPointsOnLine F K FK) ∧
  (distinctPointsOnLine G L GL) ∧
  (twoLinesIntersectAtPoint FK GL X) ∧
  (distinctPointsOnLine A O AO)
→ X.onLine AO
:= by
  sorry


theorem problem_12G3 :
∀ (A B C D E F I₁ I₂ O₁ O₂ : Point)
  (AB BC CA AD BE CF L_I₁I₂ L_O₁O₂ : Line),
  formTriangle A B C AB BC CA ∧
  A.onLine AD ∧ D.onLine AD ∧ B.onLine BC ∧ C.onLine BC ∧ D.onLine BC ∧ perpLine AD BC ∧
  B.onLine BE ∧ E.onLine BE ∧ A.onLine CA ∧ C.onLine CA ∧ E.onLine CA ∧ perpLine BE CA ∧
  C.onLine CF ∧ F.onLine CF ∧ A.onLine AB ∧ B.onLine AB ∧ F.onLine AB ∧ perpLine CF AB ∧
  inCentre I₁ A E F ∧
  inCentre I₂ B D F ∧
  circumCentre O₁ A C I₁ ∧
  circumCentre O₂ B C I₂ ∧
  I₁.onLine L_I₁I₂ ∧ I₂.onLine L_I₁I₂ ∧ distinctPointsOnLine I₁ I₂ L_I₁I₂ ∧
  O₁.onLine L_O₁O₂ ∧ O₂.onLine L_O₁O₂ ∧ distinctPointsOnLine O₁ O₂ L_O₁O₂
  → ¬(∃ P : Point, twoLinesIntersectAtPoint L_I₁I₂ L_O₁O₂ P) :=
by sorry

theorem MP92 :
∀ (A B C D E F P G H : Point)
  (AB BC CA AD EF PF CE PE GH : Line),
  formTriangle A B C AB BC CA ∧
  midpoint B D C ∧
  distinctPointsOnLine A D AD ∧
  E.onLine AD ∧
  distinctPointsOnLine E F EF ∧
  ¬(EF.intersectsLine BC) ∧
  twoLinesIntersectAtPoint EF AB F ∧
  P.onLine BC ∧
  distinctPointsOnLine P F PF ∧
  twoLinesIntersectAtPoint PF CE G ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint PE AC H ∧
  distinctPointsOnLine P E PE ∧
  distinctPointsOnLine G H GH
  → ¬(GH.intersectsLine BC)
:= by
  sorry

theorem problem_MP51 :
∀ (A B C D : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  (∠ A:B:C = ∟/3) ∧
  (∠ B:C:A = ∟/6) ∧
  midpoint B D C
  → (∠ D:A:C = ∟/12) := by
sorry

theorem problem_19G2 :
  ∀ (A B C D E F M N P Q : Point)
    (AB BC CA AD BE CF BD DF FB CD DE EC MN : Line)
    (ω_B ω_C : Circle),
  formTriangle A B C AB BC CA ∧
  twoLinesIntersectAtPoint AD BC D ∧ A.onLine AD ∧ perpLine AD BC ∧
  twoLinesIntersectAtPoint BE CA E ∧ B.onLine BE ∧ perpLine BE CA ∧
  twoLinesIntersectAtPoint CF AB F ∧ C.onLine CF ∧ perpLine CF AB ∧
  formTriangle B D F BD DF FB ∧
  formTriangle C D E CD DE EC ∧
  inCircle ω_B BD DF FB ∧
  inCircle ω_C CD DE EC ∧
  tangentAtPoint DF ω_B M ∧
  tangentAtPoint DE ω_C N ∧
  distinctPointsOnLine M N MN ∧
  P.onLine MN ∧ P.onCircle ω_B ∧ M ≠ P ∧
  Q.onLine MN ∧ Q.onCircle ω_C ∧ N ≠ Q
  → |(M─P)| = |(N─Q)| :=
by sorry

theorem problem_HP48 :
∀ (A B C I K E M N D : Point)
  (AB BC CA BI MN : Line),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  distinctPointsOnLine B I BI ∧
  perpBisector A K BI ∧
  midpoint B E C ∧
  distinctPointsOnLine M N MN ∧
  twoLinesIntersectAtPoint MN BC D
  → cyclic A K D M
:= by
  sorry

theorem problem_HP20 :
∀ (A B C D E F G H I : Point) (AB BC CA BE CD FD FE GH L : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C < ∟ ∧
  ∠B:C:A < ∟ ∧
  ∠C:A:B < ∟ ∧
  ∠A:B:C > ∠A:C:B ∧
  midpoint B F C ∧
  distinctPointsOnLine B E BE ∧
  E.onLine CA ∧
  perpLine BE CA ∧
  distinctPointsOnLine C D CD ∧
  D.onLine AB ∧
  perpLine CD AB ∧
  distinctPointsOnLine F D FD ∧
  midpoint F G D ∧
  distinctPointsOnLine F E FE ∧
  midpoint F H E ∧
  distinctPointsOnLine G H GH ∧
  A.onLine L ∧
  ¬(L.intersectsLine BC) ∧
  twoLinesIntersectAtPoint L GH I
→ |(I─A)| = |(I─F)| :=
by sorry

theorem problem_MP7 :
  ∀ (A B C D E F : Point) (AB BC CA : Line),
  formTriangle A B C AB BC CA ∧
  threePointsOnLine B C D BC ∧ between C B D ∧
  threePointsOnLine B C E BC ∧ between B C E ∧
  (∠A:B:D = 2 * (∠A:C:E)) ∧
  F.onLine BC ∧
  (∠B:A:F = ∠F:A:C)
  → |(A─B)| = |(A─C)| + |(B─F)| :=
by
  sorry

theorem problem_HP59 :
  ∀ (A B C D E F : Point) (AB BC CA BE DF CF : Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(A─C)| ∧
  midpoint A E C ∧
  between B D C ∧
  (|(B─D)| = |(C─D)| + |(C─D)|) ∧
  distinctPointsOnLine B E BE ∧
  F.onLine BE ∧
  distinctPointsOnLine D F DF ∧
  perpLine DF BE ∧
  distinctPointsOnLine C F CF
  → ∠ E:F:C = ∠ A:B:C :=
by sorry

theorem problem_HP30 :
∀ (A B C D E F O H P : Point) (AB BC CA LHD LOP : Line),
  formTriangle A B C AB BC CA
  ∧ midpoint B D C
  ∧ circumCentre O A B C
  ∧ E.onLine AB
  ∧ between A E B
  ∧ F.onLine CA
  ∧ between A F C
  ∧ (|(A─E)| = |(A─F)|)
  ∧ threePointsOnLine D H E LHD
  ∧ circumCentre P A E F
  ∧ O.onLine LOP
  ∧ P.onLine LOP
→ ¬(LHD.intersectsLine LOP)
:= by
  sorry

theorem problem_02G3 :
∀
(S : Circle)
(O A B C D E F I : Point)
(AC DA L_P L_perp CE EF FC : Line),
  (
    O.isCentre S
    ∧ A.onCircle S
    ∧ B.onCircle S
    ∧ C.onCircle S
    ∧ D.onCircle S
    ∧ E.onCircle S
    ∧ F.onCircle S
    ∧ between B O C
    ∧ ∠ A:O:B < 120
    ∧ distinctPointsOnLine A C AC
    ∧ distinctPointsOnLine A D DA
    /- “the line through O parallel to DA”: use ¬(∃ X, twoLinesIntersectAtPoint L_P DA X) to encode parallel -/
    ∧ O.onLine L_P
    ∧ ¬(∃ X : Point, twoLinesIntersectAtPoint L_P DA X)
    ∧ twoLinesIntersectAtPoint L_P AC I
    /- “the perpendicular bisector of OA meets S at E and F” -/
    ∧ perpBisector O A L_perp
    ∧ E.onLine L_perp
    ∧ F.onLine L_perp
    ∧ formTriangle C E F CE EF FC
  )
  → inCentre I C E F
:= by
  sorry

theorem problem_imo_2013_p4 :
  ∀ (A B C H W M N X Y : Point)
    (AB BC CA BM CN ℓ : Line)
    (ω₁ ω₂ : Circle),
  formTriangle A B C AB BC CA ∧
  W.onLine BC ∧
  between B W C ∧
  M.onLine CA ∧
  distinctPointsOnLine B M BM ∧
  perpLine BM CA ∧
  N.onLine AB ∧
  distinctPointsOnLine C N CN ∧
  perpLine CN AB ∧
  twoLinesIntersectAtPoint BM CN H ∧
  circumCircle ω₁ B W N ∧
  X.onCircle ω₁ ∧
  ∠W:N:X = ∟ ∧
  circumCircle ω₂ C W M ∧
  Y.onCircle ω₂ ∧
  ∠W:M:Y = ∟
  → threePointsOnLine X Y H ℓ
:= by
  sorry

theorem problem_15G7 :
∀
(A B C D P Q R S O : Point)
(AB BC CD DA AP PO OS SA BQ QO OP PB CR RO OQ QC DS SO OR RD PR QS AC PQ RS : Line)
(inc1 inc2 inc3 inc4 : Circle),
  formQuadrilateral A B C D AB BC CD DA
∧ A.onLine AB ∧ B.onLine AB
∧ B.onLine BC ∧ C.onLine BC
∧ C.onLine CD ∧ D.onLine CD
∧ D.onLine DA ∧ A.onLine DA

∧ A.onLine AP ∧ P.onLine AP
∧ P.onLine PO ∧ O.onLine PO
∧ O.onLine OS ∧ S.onLine OS
∧ S.onLine SA ∧ A.onLine SA
∧ tangentLine AP inc1 ∧ tangentLine PO inc1 ∧ tangentLine OS inc1 ∧ tangentLine SA inc1

∧ B.onLine BQ ∧ Q.onLine BQ
∧ Q.onLine QO ∧ O.onLine QO
∧ O.onLine OP ∧ P.onLine OP
∧ P.onLine PB ∧ B.onLine PB
∧ tangentLine BQ inc2 ∧ tangentLine QO inc2 ∧ tangentLine OP inc2 ∧ tangentLine PB inc2

∧ C.onLine CR ∧ R.onLine CR
∧ R.onLine RO ∧ O.onLine RO
∧ O.onLine OQ ∧ Q.onLine OQ
∧ Q.onLine QC ∧ C.onLine QC
∧ tangentLine CR inc3 ∧ tangentLine RO inc3 ∧ tangentLine OQ inc3 ∧ tangentLine QC inc3

∧ D.onLine DS ∧ S.onLine DS
∧ S.onLine SO ∧ O.onLine SO
∧ O.onLine OR ∧ R.onLine OR
∧ R.onLine RD ∧ D.onLine RD
∧ tangentLine DS inc4 ∧ tangentLine SO inc4 ∧ tangentLine OR inc4 ∧ tangentLine RD inc4

∧ P.onLine PR ∧ R.onLine PR
∧ Q.onLine QS ∧ S.onLine QS
∧ A.onLine AC ∧ C.onLine AC
∧ P.onLine PQ ∧ Q.onLine PQ
∧ R.onLine RS ∧ S.onLine RS
∧ twoLinesIntersectAtPoint PR QS O

→
  ( ∃ X : Point, X.onLine AC ∧ X.onLine PQ ∧ X.onLine RS )
  ∨
  ( ¬(AC.intersectsLine PQ) ∧ ¬(PQ.intersectsLine RS) ∧ ¬(AC.intersectsLine RS) )
:= by
  sorry

theorem problem_imo_2003_p4 :
  ∀ (A B C D P Q R M : Point)
    (AB BC CD DA AC DP DQ DR BM DM : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  P.onLine BC ∧ distinctPointsOnLine D P DP ∧ perpLine DP BC ∧
  Q.onLine CA ∧ distinctPointsOnLine D Q DQ ∧ perpLine DQ CA ∧
  R.onLine AB ∧ distinctPointsOnLine D R DR ∧ perpLine DR AB ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B M BM ∧
  distinctPointsOnLine D M DM
  →
  (
    ( (|(P─Q)| = |(Q─R)|)
      ∧ (∠A:B:M = ∠M:B:C ∧ ∠A:D:M = ∠M:D:C ∧ M.onLine AC ∧ between A M C)
    )
    ∨
    (
      ¬(|(P─Q)| = |(Q─R)|)
      ∧ ¬(∠A:B:M = ∠M:B:C ∧ ∠A:D:M = ∠M:D:C ∧ M.onLine AC ∧ between A M C)
    )
  )
:= by
  sorry

theorem problem_HP85 :
∀ (A B C D E F G : Point)
  (AB BC CA BD CE AF AG DE GF : Line),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| > |(A─C)|) ∧
  distinctPointsOnLine B D BD ∧ perpLine BD CA ∧ twoLinesIntersectAtPoint BD CA D ∧
  distinctPointsOnLine C E CE ∧ perpLine CE AB ∧ twoLinesIntersectAtPoint CE AB E ∧
  midpoint B F C ∧
  distinctPointsOnLine A F AF ∧
  perpLine AG AF ∧ distinctPointsOnLine A G AG ∧ twoLinesIntersectAtPoint DE AG G ∧ distinctPointsOnLine D E DE ∧
  distinctPointsOnLine G F GF
  → ∠G:F:A = ∠A:F:C
:= by
  sorry

theorem problem_MP95 :
  ∀ (A B C D E F G : Point) (AB BC CD DA BD AF DE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  AB.intersectsLine CD ∧
  ¬(DE.intersectsLine AB) ∧
  twoLinesIntersectAtPoint DE BC E ∧
  ¬(AF.intersectsLine DC) ∧
  twoLinesIntersectAtPoint AF BC F ∧
  twoLinesIntersectAtPoint AF BD G
  → (|(B─E)| * |(G─F)|) = (|(E─C)| * |(A─G)|) :=
by sorry


theorem problem_HP6 :
∀ (A B C D E F G J O : Point) (Γ : Circle)
  (BJA BC BD AB AC DE AO : Line),
  O.isCentre Γ ∧
  tangentAtPoint BC Γ C ∧
  tangentAtPoint BD Γ D ∧
  A.onCircle Γ ∧
  J.onCircle Γ ∧
  threePointsOnLine B J A BJA ∧
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine D E DE ∧
  distinctPointsOnLine A O AO ∧
  twoLinesIntersectAtPoint DE AO E ∧
  perpLine DE AO ∧
  twoLinesIntersectAtPoint DE AB F ∧
  twoLinesIntersectAtPoint AC DE G
  → |(D─F)| = |(F─G)| :=
by sorry

theorem problem_88T15 :
∀
(A B C H_A H_B H_C M_A N_A M_B N_B M_C N_C X : Point)
(AB BC CA AH_A BH_B CH_C M_AN_A M_BN_B M_CN_C L_A L_B L_C : Line)
(S_A S_B S_C : Circle),
formTriangle A B C AB BC CA ∧

H_A.onLine BC ∧ between B H_A C ∧ distinctPointsOnLine A H_A AH_A ∧ perpLine AH_A BC ∧
A.onCircle S_A ∧ H_A.onCircle S_A ∧
M_A.onCircle S_A ∧ M_A.onLine AB ∧ A≠ M_A ∧
N_A.onCircle S_A ∧ N_A.onLine AC ∧ A ≠  N_A ∧
distinctPointsOnLine M_A N_A M_AN_A ∧
A.onLine L_A ∧ perpLine L_A M_AN_A ∧

H_B.onLine CA ∧ between A H_B C ∧ distinctPointsOnLine B H_B BH_B ∧ perpLine BH_B CA ∧
B.onCircle S_B ∧ H_B.onCircle S_B ∧
M_B.onCircle S_B ∧ M_B.onLine BA ∧ B ≠  M_B ∧
N_B.onCircle S_B ∧ N_B.onLine BC ∧ B ≠ N_B ∧
distinctPointsOnLine M_B N_B M_BN_B ∧
B.onLine L_B ∧ perpLine L_B M_BN_B ∧

H_C.onLine AB ∧ between A H_C B ∧ distinctPointsOnLine C H_C CH_C ∧ perpLine CH_C AB ∧
C.onCircle S_C ∧ H_C.onCircle S_C ∧
M_C.onCircle S_C ∧ M_C.onLine CA ∧ C ≠  M_C ∧
N_C.onCircle S_C ∧ N_C.onLine CB ∧ C ≠ N_C ∧
distinctPointsOnLine M_C N_C M_CN_C ∧
C.onLine L_C ∧ perpLine L_C M_CN_C

→ twoLinesIntersectAtPoint L_A L_B X ∧ X.onLine L_C
:= by
  sorry

theorem problem_16G6 :
∀ (A B C D E F P M X Y Q : Point)
  (AB BC CD DA AC BE DF BM DM XE YF PQ : Line)
  (ω : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  (∠ A:B:C = ∠ A:D:C) ∧
  (∠ A:B:C < ∟) ∧

  distinctPointsOnLine A C AC ∧
  E.onLine AC ∧
  (∠ A:B:E = ∠ E:B:C) ∧
  F.onLine AC ∧
  (∠ A:D:F = ∠ F:D:C) ∧
  twoLinesIntersectAtPoint BE DF P ∧
  midpoint A M C ∧
  circumCircle ω B P D ∧

  B.onLine BM ∧
  M.onLine BM ∧
  X.onLine BM ∧
  X.onCircle ω ∧
  D.onLine DM ∧
  M.onLine DM ∧
  Y.onLine DM ∧
  Y.onCircle ω ∧

  X.onLine XE ∧
  E.onLine XE ∧
  Y.onLine YF ∧
  F.onLine YF ∧
  twoLinesIntersectAtPoint XE YF Q ∧

  P.onLine PQ ∧
  Q.onLine PQ
→ perpLine PQ AC
:= by
  sorry

theorem problem_15G3 :
∀
(A B C D H M P Q R : Point)
(AB BC CA CH BH AD BD PQ CQ : Line)
(Γ : Circle),
formTriangle A B C AB BC CA ∧
∠B:C:A = ∟ ∧
distinctPointsOnLine A B AB ∧
distinctPointsOnLine C H CH ∧
H.onLine AB ∧
perpLine CH AB ∧
formTriangle C B H CB BH HC ∧
insideTriangle D C B H CB BH HC ∧
distinctPointsOnLine A D AD ∧
twoLinesIntersectAtPoint AD CH M ∧
midpoint A M D ∧
distinctPointsOnLine B D BD ∧
twoLinesIntersectAtPoint BD CH P ∧
B.onCircle Γ ∧
D.onCircle Γ ∧
distinctPointsOnLine P Q PQ ∧
Q.onCircle Γ ∧
tangentAtPoint PQ Γ Q ∧
distinctPointsOnLine C Q CQ ∧
twoLinesIntersectAtPoint CQ AD R
→ R.onCircle Γ
:= by
  sorry

theorem problem_HP64 :
  ∀ (A B C D E F : Point) (AB AC BF CD : Line) (O P : Circle),
    distinctPointsOnLine A B AB ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine C D CD ∧
    tangentAtPoint AB O A ∧
    tangentAtPoint AC O B ∧
    D.onLine AB ∧
    circumCircle P A D C ∧
    E.onCircle O ∧
    E.onCircle P ∧
    twoLinesIntersectAtPoint BF CD F ∧
    perpLine BF CD
  → ∠D:E:F = 2 * ∠A:D:C :=
by
  sorry

theorem problem_82T13 :
∀ (A₁ A₂ A₃ I M₁ M₂ M₃ T₁ T₂ T₃ S₁ S₂ S₃ : Point)
  (A₁A₂ A₂A₃ A₃A₁ M₁S₁ M₂S₂ M₃S₃ : Line)
  (incΩ : Circle),
  ( |(A₁─A₂)| ≠ |(A₂─A₃)| ∧ |(A₂─A₃)| ≠ |(A₃─A₁)| ∧ |(A₃─A₁)| ≠ |(A₁─A₂)| )
  ∧ formTriangle A₁ A₂ A₃ A₁A₂ A₂A₃ A₃A₁
  ∧ inCentre I A₁ A₂ A₃
  ∧ inCircle incΩ A₁A₂ A₂A₃ A₃A₁
  ∧ T₁.onLine A₂A₃ ∧ T₁.onCircle incΩ ∧ tangentAtPoint A₂A₃ incΩ T₁
  ∧ T₂.onLine A₃A₁ ∧ T₂.onCircle incΩ ∧ tangentAtPoint A₃A₁ incΩ T₂
  ∧ T₃.onLine A₁A₂ ∧ T₃.onCircle incΩ ∧ tangentAtPoint A₁A₂ incΩ T₃
  ∧ midpoint A₂ M₁ A₃
  ∧ midpoint A₁ M₂ A₃
  ∧ midpoint A₁ M₃ A₂
  ∧ (¬(A₁ = T₁) ∧ ¬(A₁ = S₁)  -- schematic placeholder for “S₁ is reflection of T₁ about the bisector of ∠A₁”
     ∧ ¬(A₂ = T₂) ∧ ¬(A₂ = S₂)
     ∧ ¬(A₃ = T₃) ∧ ¬(A₃ = S₃))
  ∧ distinctPointsOnLine M₁ S₁ M₁S₁
  ∧ distinctPointsOnLine M₂ S₂ M₂S₂
  ∧ distinctPointsOnLine M₃ S₃ M₃S₃
  →
  ∃ X : Point,
    twoLinesIntersectAtPoint M₁S₁ M₂S₂ X
    ∧ X.onLine M₃S₃
:= by
  sorry

theorem problem_imo_2015_p3 :
  ∀ (A B C H F M K Q : Point)
    (AB BC CA : Line)
    (Γ α β: Circle),
  formTriangle A B C AB BC CA ∧
  (|(A─B)| > |(A─C)|) ∧
  circumCircle Γ A B C ∧
  A.onCircle Γ ∧ B.onCircle Γ ∧ C.onCircle Γ ∧ K.onCircle Γ ∧ Q.onCircle Γ ∧
  midpoint B M C ∧
  F.onLine BC ∧
  perpLine AB BC ∧  -- (Placeholder; ordinarily one would encode “F is foot of altitude”, “H is orthocenter” etc.)
  perpLine AC BC ∧  -- (Likewise placeholder to suggest orthogonality conditions in an acute triangle)
  ∠H:K:Q = ∟ ∧
  circumCircle α K Q H ∧
  circumCircle β F K M
  → (∀ X : Point, X.onCircle α ∧ X.onCircle β → X = K)
:= by
  sorry

theorem problem_HP17 :
  ∀ (A B C I D E F G : Point)
    (AB BC CA AD IE EF : Line)
    (Γ : Circle),
    formTriangle A B C AB BC CA ∧
    inCentre I A B C ∧
    inCircle Γ AB BC CA ∧
    I.isCentre Γ ∧
    tangentAtPoint BC Γ D ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine I E IE ∧
    twoLinesIntersectAtPoint IE BC E ∧
    distinctPointsOnLine E F EF ∧
    twoLinesIntersectAtPoint EF AB F ∧
    twoLinesIntersectAtPoint EF AC G ∧
    tangentAtPoint EF Γ E ∧
    ¬(∃ X : Point, twoLinesIntersectAtPoint AD IE X)
  → midpoint F E G :=
by sorry

theorem problem_HP67 :
∀
(A B C D E F G H I O : Point)
(AB BC CA DE GF AI AO DH EH : Line)
(Ω : Circle),
(
  formTriangle A B C AB BC CA
  ∧ midpoint A D B
  ∧ midpoint A E C
  ∧ distinctPointsOnLine D H DH
  ∧ F.onLine DH
  ∧ F.onCircle Ω
  ∧ distinctPointsOnLine E H EH
  ∧ G.onLine EH
  ∧ G.onCircle Ω
  ∧ distinctPointsOnLine D E DE
  ∧ distinctPointsOnLine G F GF
  ∧ twoLinesIntersectAtPoint DE GF I
  ∧ distinctPointsOnLine A I AI
  ∧ distinctPointsOnLine A O AO
  ∧ O.isCentre Ω
  ∧ circumCircle Ω A B C
)
→ perpLine AI AO
:= by
  sorry

theorem problem_HP66 :
  ∀ (A B C D E G H J K : Point) (AB BC CA : Line) (O I P : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  inCircle I AB BC CA ∧
  tangentAtPoint AB I D ∧
  tangentAtPoint AC I E ∧
  O.intersectsCircle P ∧
  J.onCircle O ∧
  J.onCircle P ∧
  tangentAtPoint AB P G ∧
  tangentAtPoint AC P H ∧
  K.onLine AB ∧
  K.onCircle P
  → (|(A ─ J)| = |(A ─ K)| ∧ ∠ B:A:J = ∠ C:A:D) := by
sorry

theorem HP26 :
∀ (A B C D E F G H O : Point)
  (AB BC CA AD BD CD OE OF AH BH CH HG : Line)
  (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  O.isCentre Γ ∧
  distinctPointsOnLine A D AD ∧
  ∠B:A:D = ∠D:A:C ∧
  D.onCircle Γ ∧
  distinctPointsOnLine O E OE ∧
  distinctPointsOnLine B D BD ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint BD OE X) ∧
  twoLinesIntersectAtPoint AB OE E ∧
  distinctPointsOnLine O F OF ∧
  distinctPointsOnLine C D CD ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint CD OF X) ∧
  twoLinesIntersectAtPoint AC OF F ∧
  distinctPointsOnLine A H AH ∧
  perpLine AH BC ∧
  distinctPointsOnLine B H BH ∧
  perpLine BH AC ∧
  distinctPointsOnLine C H CH ∧
  perpLine CH AB ∧
  distinctPointsOnLine H G HG ∧
  twoLinesIntersectAtPoint BC HG G ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint HG AD X)
  → ( |(B─E)| = |(G─E)| )
    ∧ ( |(G─E)| = |(G─F)| )
    ∧ ( |(G─F)| = |(C─F)| ) :=
by sorry

theorem HP24 :
  ∀ (A B C D E F G : Point)
    (AB BC CA AE DF : Line)
    (I O : Circle),
  formTriangle A B C AB BC CA ∧
  inCircle I AB BC CA ∧
  tangentAtPoint BC I D ∧
  twoLinesIntersectAtPoint AE BC E ∧
  perpLine AE BC ∧
  midpoint A F E ∧
  distinctPointsOnLine D F DF ∧
  G.onLine DF ∧
  G.onCircle I ∧
  circumCircle O B C G
  → ∃ (L : Line), tangentAtPoint L O G ∧ tangentAtPoint L I G
:= by
  sorry

theorem HP9 :
∀ (O : Circle) (P C D E A B M N : Point) (PC PD AB OE CD PN : Line),
P.outsideCircle O ∧
tangentAtPoint PC O C ∧
tangentAtPoint PD O D ∧
E.onCircle O ∧
tangentAtPoint AB O E ∧
twoLinesIntersectAtPoint PC AB A ∧
twoLinesIntersectAtPoint PD AB B ∧
twoLinesIntersectAtPoint OE CD N ∧
twoLinesIntersectAtPoint PN AB M
→ |(M─A)| = |(M─B)| := by
sorry

theorem problem_HP45 :
∀ (A B C D E O P : Point)
  (lPA lPBC lOP lAD : Line)
  (Ocircle Γ : Circle),
  (A.onLine lPA) ∧
  (P.onLine lPA) ∧
  (O.isCentre Ocircle) ∧
  (A.onCircle Ocircle) ∧
  tangentAtPoint lPA Ocircle A ∧
  (B.onLine lPBC) ∧
  (C.onLine lPBC) ∧
  (B.onCircle Ocircle) ∧
  (C.onCircle Ocircle) ∧
  (O.onLine lOP) ∧
  (P.onLine lOP) ∧
  twoLinesIntersectAtPoint lAD lOP D ∧
  perpLine lAD lOP ∧
  circumCircle Γ A D C ∧
  (E.onLine lPBC) ∧
  (E.onCircle Γ)
  → ∠ B:A:E = ∠ A:C:B
:= by
  sorry

theorem HP41 :
∀ (P A B C D E F : Point)
  (PA PB AB BD CF PCD : Line)
  (O : Circle),
  (
    distinctPointsOnLine P A PA
    ∧ tangentAtPoint PA O A
    ∧ A.onCircle O
    ∧ distinctPointsOnLine P B PB
    ∧ tangentAtPoint PB O B
    ∧ B.onCircle O
    ∧ threePointsOnLine P C D PCD
    ∧ C.onCircle O
    ∧ D.onCircle O
    ∧ distinctPointsOnLine A B AB
    ∧ distinctPointsOnLine B D BD
    ∧ distinctPointsOnLine C F CF
    ∧ ¬(∃ X : Point, twoLinesIntersectAtPoint PB CF X)
    ∧ twoLinesIntersectAtPoint CF AB E
    ∧ twoLinesIntersectAtPoint CF BD F
  )
  → midpoint C E F
:= by
  sorry

theorem problem_12G2 :
∀ (A B C D E F G H M : Point)
  (AB BC CD DA AC BD EC CG GD DE : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  cyclic A B C D ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint AC BD E ∧
  twoLinesIntersectAtPoint DA BC F ∧
  formQuadrilateral E C G D EC CG GD DE ∧
  midpoint M E G ∧
  midpoint M C D ∧
  perpBisector E H AD
→ cyclic D H F G := by
  sorry

theorem problem_HP19 :
∀ (A B C I E D F G : Point) (AB BC CA DE IF : Line) (O : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  inCentre I A B C ∧
  threePointsOnLine B C D BC ∧
  distinctPointsOnLine D E DE ∧
  twoLinesIntersectAtPoint IF DE F ∧
  perpLine IF DE ∧
  G.onLine IF ∧
  G.onCircle O
  → midpoint I G F :=
by
  sorry

theorem problem_15G1 :
∀ (A B C H G I J : Point) (AB BC CA BG GH HA : Line) (Ω : Circle),
  formTriangle A B C AB BC CA
  ∧ insideTriangle H A B C AB BC CA
  ∧ perpLine BC AH
  ∧ perpLine AC BH
  ∧ perpLine AB CH
  ∧ formQuadrilateral A B G H AB BG GH HA
  ∧ (|(A─B)| = |(G─H)|)
  ∧ (|(B─G)| = |(A─H)|)
  ∧ I.onLine GH
  ∧ (∃ (X : Point), X.onLine AC ∧ midpoint H X I)
  ∧ circumCircle Ω G C I
  ∧ J.onLine AC
  ∧ J.onCircle Ω
→ |(I─J)| = |(A─H)| :=
by sorry

theorem problem_09G3 :
∀
(A B C Y Z G R S : Point)
(AB BC CA BY CZ CY YR RB CS SZ ZB : Line)
(incircle : Circle),
formTriangle A B C AB BC CA ∧
inCircle incircle AB BC CA ∧
tangentLine AB incircle ∧ Z.onLine AB ∧ Z.onCircle incircle ∧
tangentLine AC incircle ∧ Y.onLine AC ∧ Y.onCircle incircle ∧
twoLinesIntersectAtPoint BY CZ G ∧
formQuadrilateral B C Y R BC CY YR RB ∧
formQuadrilateral B C S Z BC CS SZ ZB ∧
|(B─C)|=|(Y─R)| ∧ |(C─Y)|=|(R─B)| ∧
|(B─C)|=|(S─Z)| ∧ |(C─S)|=|(Z─B)|
→ |(G─R)|=|(G─S)| := by
  sorry

theorem problem_09G6 :
∀ (A B C D P O₁ O₂ H₁ H₂ E₁ E₂ : Point)
  (AB BC CD DA L₁ L₂ L₃ : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  twoLinesIntersectAtPoint DA BC P ∧
  (∃ M : Point, twoLinesIntersectAtPoint AB CD M) ∧
  circumCentre O₁ A B P ∧
  circumCentre O₂ D C P ∧
  orthoCentre H₁ A B P ∧   -- new predicate for “H₁ is the orthocenter of △ABP”
  orthoCentre H₂ D C P ∧   -- new predicate for “H₂ is the orthocenter of △DCP”
  midpoint O₁ E₁ H₁ ∧
  midpoint O₂ E₂ H₂ ∧
  distinctPointsOnLine H₁ H₂ L₃ ∧
  E₁.onLine L₁ ∧ perpLine L₁ CD ∧
  E₂.onLine L₂ ∧ perpLine L₂ AB
  → ∃ X : Point, X.onLine L₁ ∧ X.onLine L₂ ∧ X.onLine L₃ :=
by sorry

theorem problem_HP1 :
∀ (P E F A B C D : Point) (O : Circle)
  (PE PF PB AF BE : Line),
  tangentAtPoint PE O E ∧
  tangentAtPoint PF O F ∧
  A.onCircle O ∧ B.onCircle O ∧ A ≠ B ∧
  threePointsOnLine P B C PB ∧ B.onCircle O ∧ C.onCircle O ∧ B ≠ C ∧
  distinctPointsOnLine A F AF ∧ distinctPointsOnLine B E BE ∧
  twoLinesIntersectAtPoint AF BE D
  → ∠ P:C:D = ∠ P:C:E
:= by
  sorry

theorem problem_MP56 :
∀ (A B C D E F G H O : Point)
  (AB BC CD DA AC BD AE DH : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  twoLinesIntersectAtPoint AC BD O ∧
  twoLinesIntersectAtPoint AE BC E ∧
  ∠B:A:E = ∠E:A:C ∧
  twoLinesIntersectAtPoint AE DH H ∧
  perpLine AE DH ∧
  D.onLine DH ∧
  twoLinesIntersectAtPoint DH AB F ∧
  twoLinesIntersectAtPoint DH AC G
  → |(B─F)| = |(O─G)| + |(O─G)| :=
by
  sorry

theorem problem_HP40 :
  ∀ (A B C D E F G H : Point)
    (AB BC CD DA AF CE BG DH : Line)
    (O P : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint AB DC X) ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint BC AD X) ∧
  E.onLine DA ∧
  F.onLine CD ∧
  twoLinesIntersectAtPoint AF CE G ∧
  circumCircle O A E G ∧
  circumCircle P C F G ∧
  H.onCircle O ∧
  H.onCircle P
  → (∠ G:B:A = ∠ H:D:A) :=
by sorry

theorem problem_82T20 :
  ∀ (A B C D M N P Q : Point)
    (AB BC CD DA MN NP PQ QM : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine M N MN ∧
  distinctPointsOnLine N P NP ∧
  distinctPointsOnLine P Q PQ ∧
  distinctPointsOnLine Q M QM ∧
  (|(A─B)| = |(B─M)| ∧ |(B─M)| = |(A─M)|) ∧
  (|(C─D)| = |(D─P)| ∧ |(D─P)| = |(C─P)|) ∧
  (|(B─C)| = |(C─N)| ∧ |(C─N)| = |(B─N)|) ∧
  (|(A─D)| = |(D─Q)| ∧ |(D─Q)| = |(A─Q)|)
  → (|(M─N)| = |(A─C)| ∧ formQuadrilateral M N P Q MN NP PQ QM)
:= by
  sorry

theorem problem_HP46 :
∀ (A B C D E F G : Point)
  (AB BC CD DA BD CE CF EF AC GC : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬(AB.intersectsLine DC) ∧
  ¬(BC.intersectsLine AD) ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine C E CE ∧
  perpLine CE AB ∧
  E.onLine AB ∧
  distinctPointsOnLine C F CF ∧
  perpLine CF AD ∧
  F.onLine AD ∧
  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint EF BD G ∧
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine G C GC
  → perpLine GC AC := by
sorry

theorem problem_HP29 :
∀
(A B C D E F G H I : Point)
(AB BC CD DA EF AG HC AI GC : Line)
(O P : Circle),
formQuadrilateral A B C D AB BC CD DA ∧
A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O ∧
distinctPointsOnLine A B AB ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine C D CD ∧ distinctPointsOnLine D A DA ∧
twoLinesIntersectAtPoint AB CD E ∧
twoLinesIntersectAtPoint DA BC F ∧
distinctPointsOnLine E F EF ∧
circumCircle P E F C ∧
G.onCircle P ∧ G.onCircle O ∧
distinctPointsOnLine A G AG ∧
twoLinesIntersectAtPoint AG EF H ∧
distinctPointsOnLine H C HC ∧
I.onCircle O ∧ I.onLine HC ∧
distinctPointsOnLine A I AI ∧
distinctPointsOnLine G C GC
→ ∃ (X : Point), X.onLine AI ∧ X.onLine GC ∧ X.onLine EF :=
by sorry

theorem problem_09G8 :
  ∀ (A B C D M N I₁ I₂ I₃ H : Point)
    (AB BC CD DA l : Line)
    (incircle : Circle),
  formQuadrilateral A B C D AB BC CD DA ∧
  tangentLine AB incircle ∧
  tangentLine BC incircle ∧
  tangentLine CD incircle ∧
  tangentLine DA incircle ∧
  A.onLine l ∧
  M.onLine l ∧
  M.onLine BC ∧
  N.onLine l ∧
  N.onLine CD ∧
  inCentre I₁ A B M ∧
  inCentre I₂ M N C ∧
  inCentre I₃ N D A ∧
  orthoCentre I₁ I₂ I₃ H
  →
  H.onLine l
:= by
  sorry

theorem problem_96G1 :
∀
(A B C H P E Q R X : Point)
(AB BC CA BP AP CP BE AQ BQ AR CR HR EX : Line)
(Ω : Circle),
formTriangle A B C AB BC CA ∧
circumCircle Ω A B C ∧
P.onCircle Ω ∧
¬(P = A) ∧ ¬(P = B) ∧ ¬(P = C) ∧
A.onLine AB ∧ B.onLine AB ∧
B.onLine BC ∧ C.onLine BC ∧
C.onLine CA ∧ A.onLine CA ∧
E.onLine AC ∧ B.onLine BE ∧ E.onLine BE ∧ perpLine AC BE ∧
distinctPointsOnLine B P BP ∧
distinctPointsOnLine A P AP ∧
distinctPointsOnLine C P CP ∧
distinctPointsOnLine A Q AQ ∧ (∀ Z, ¬(twoLinesIntersectAtPoint AQ BP Z)) ∧
distinctPointsOnLine B Q BQ ∧ (∀ Z, ¬(twoLinesIntersectAtPoint BQ AP Z)) ∧
twoLinesIntersectAtPoint AQ BQ Q ∧
distinctPointsOnLine A R AR ∧ (∀ Z, ¬(twoLinesIntersectAtPoint AR CP Z)) ∧
distinctPointsOnLine C R CR ∧ (∀ Z, ¬(twoLinesIntersectAtPoint CR AP Z)) ∧
twoLinesIntersectAtPoint AR CR R ∧
distinctPointsOnLine H R HR ∧
twoLinesIntersectAtPoint HR AQ X ∧
distinctPointsOnLine E X EX
→ ¬(∃ Z : Point, twoLinesIntersectAtPoint EX AP Z) :=
by sorry

theorem problem_18G5 :
∀ (A B C I D E F P Q R : Point)
  (AB BC CA AI BI CI l L1 L2 L3 PQ QR RP : Line)
  (ω Θ : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  distinctPointsOnLine A I AI ∧
  distinctPointsOnLine B I BI ∧
  distinctPointsOnLine C I CI ∧
  twoLinesIntersectAtPoint l AI D ∧
  twoLinesIntersectAtPoint l BI E ∧
  twoLinesIntersectAtPoint l CI F ∧
  ¬(A.onLine l) ∧
  ¬(B.onLine l) ∧
  ¬(C.onLine l) ∧
  ¬(I.onLine l) ∧
  perpBisector A D L1 ∧
  perpBisector B E L2 ∧
  perpBisector C F L3 ∧
  twoLinesIntersectAtPoint L1 L2 P ∧
  twoLinesIntersectAtPoint L2 L3 Q ∧
  twoLinesIntersectAtPoint L3 L1 R ∧
  formTriangle P Q R PQ QR RP ∧
  circumCircle ω A B C ∧
  circumCircle Θ P Q R
→ ∃ X : Point, X.onCircle Θ ∧ X.onCircle ω ∧ ∀ Y, Y.onCircle Θ ∧ Y.onCircle ω → Y = X
:= by
  sorry

theorem problem_imo_2019_p2 :
∀ (A B C A_1 B_1 P Q P_1 Q_1 : Point) (AB BC CA PQ : Line),
  formTriangle A B C AB BC CA ∧
  A_1.onLine BC ∧ between B A_1 C ∧
  B_1.onLine CA ∧ between A B_1 C ∧
  between A P A_1 ∧
  between B Q B_1 ∧
  distinctPointsOnLine P Q PQ ∧
  ¬ (∃ X : Point, twoLinesIntersectAtPoint PQ AB X) ∧
  between P B_1 P_1 ∧
  between Q A_1 Q_1 ∧
  ∠P:P_1:C = ∠B:A:C ∧
  ∠C:Q_1:Q = ∠C:B:A
→ cyclic P Q P_1 Q_1 := by
sorry

theorem problem_MP98 :
  ∀ (A B C D P E F G H : Point)
    (AB BC CD DA AC BD PE PF EF : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  P.onLine BC ∧

  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine B D BD ∧

  distinctPointsOnLine P E PE ∧
  twoLinesIntersectAtPoint AB PE E ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint PE AC X) ∧

  distinctPointsOnLine P F PF ∧
  twoLinesIntersectAtPoint CD PF F ∧
  ¬(∃ X : Point, twoLinesIntersectAtPoint PF BD X) ∧

  distinctPointsOnLine E F EF ∧
  twoLinesIntersectAtPoint EF BD G ∧
  twoLinesIntersectAtPoint EF AC H

  → True
:= by
  sorry

theorem problem_HP36 :
∀ (A B C D E F G H I : Point)
  (AB BC CA BD CE AF AD DE EA GF : Line)
  (O P : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle O A B C ∧
  distinctPointsOnLine A F AF ∧
  F.onCircle O ∧
  (∠ B:A:F = ∠ F:A:C) ∧
  perpLine BD AC ∧
  distinctPointsOnLine B D BD ∧
  twoLinesIntersectAtPoint BD AC D ∧
  perpLine CE AB ∧
  distinctPointsOnLine C E CE ∧
  twoLinesIntersectAtPoint CE AB E ∧
  twoLinesIntersectAtPoint BD CE H ∧
  formTriangle A D E AD DE EA ∧
  circumCircle P A D E ∧
  G.onCircle O ∧
  G.onCircle P ∧
  distinctPointsOnLine G F GF ∧
  twoLinesIntersectAtPoint GF BC I
  → (∠ B:H:I = ∠ I:H:C) :=
by
  sorry

theorem problem_imo_2005_p5 :
∀ (A B C D P X G : Point)
  (AB BC CD DA AC BD : Line),
  formQuadrilateral A B C D AB BC CD DA
  ∧ |(B─C)| = |(D─A)|
  ∧ twoLinesIntersectAtPoint AC BD P
  ∧ twoLinesIntersectAtPoint BC DA G
  → ( X ≠ P
    ∧ ∀ (E F Q R : Point) (EF : Line),
        E.onLine BC
        ∧ between B E C
        ∧ F.onLine DA
        ∧ between D F A
        ∧ |(B─E)| = |(D─F)|
        ∧ twoLinesIntersectAtPoint BD EF Q
        ∧ twoLinesIntersectAtPoint EF AC R
        → cyclic P Q R X ) :=
by sorry

theorem problem_14G7 :
  ∀ (A B C I U V X Y W Z : Point)
    (AB BC CA LIXY LIWZ : Line)
    (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  circumCircle Γ A B C ∧
  inCentre I A B C ∧
  U.onLine BC ∧
  V.onCircle Γ ∧
  midpoint A W X ∧
  midpoint B Z C ∧
  threePointsOnLine I X Y LIXY
  → threePointsOnLine I W Z LIWZ
:= by
  sorry

theorem problem_imo_2000_p6 :
∀ (A B C H1 H2 H3 T1 T2 T3 : Point)
  (AB BC CA AH1 BH2 CH3 T1T2 T2T3 T3T1 : Line)
  (ω : Circle),
  formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A H1 AH1 ∧ twoLinesIntersectAtPoint BC AH1 H1 ∧ perpLine AH1 BC ∧
  distinctPointsOnLine B H2 BH2 ∧ twoLinesIntersectAtPoint CA BH2 H2 ∧ perpLine BH2 CA ∧
  distinctPointsOnLine C H3 CH3 ∧ twoLinesIntersectAtPoint AB CH3 H3 ∧ perpLine CH3 AB ∧
  inCircle ω AB BC CA ∧
  T1.onLine BC ∧ T1.onCircle ω ∧ tangentAtPoint BC ω T1 ∧
  T2.onLine CA ∧ T2.onCircle ω ∧ tangentAtPoint CA ω T2 ∧
  T3.onLine AB ∧ T3.onCircle ω ∧ tangentAtPoint AB ω T3
→ (
  -- Conclusion (informal description, since reflections are not among the given primitives):
  -- “The reflections of the lines H1H2, H2H3, and H3H1 with respect to the lines T1T2, T2T3, and T3T1
  -- form a triangle whose vertices lie on the circle ω.”
  True
)
:= by
  sorry

theorem HP57 :
∀ (P A B C D E F G O : Point)
  (PA PB AB OC PD CE : Line)
  (Γ : Circle),
  O.isCentre Γ ∧
  A.onCircle Γ ∧
  B.onCircle Γ ∧
  C.onCircle Γ ∧
  distinctPointsOnLine P A PA ∧
  distinctPointsOnLine P B PB ∧
  tangentAtPoint PA Γ A ∧
  tangentAtPoint PB Γ B ∧
  distinctPointsOnLine O C OC ∧
  distinctPointsOnLine A B AB ∧
  twoLinesIntersectAtPoint AB OC D ∧
  distinctPointsOnLine P D PD ∧
  threePointsOnLine C E F CE ∧
  twoLinesIntersectAtPoint CE PA E ∧
  twoLinesIntersectAtPoint CE PB F ∧
  tangentAtPoint CE Γ C ∧
  twoLinesIntersectAtPoint PD CE G
  → midpoint E G F :=
by
  sorry

theorem problem_95G1 :
  ∀ (A B C D X Y Z P M N T : Point)
    (l xy am dn : Line)
    (α β : Circle),
  distinctPointsOnLine A B l ∧ C.onLine l ∧ D.onLine l ∧
  A.onCircle α ∧ C.onCircle α ∧
  B.onCircle β ∧ D.onCircle β ∧
  X.onCircle α ∧ X.onCircle β ∧
  Y.onCircle α ∧ Y.onCircle β ∧
  distinctPointsOnLine X Y xy ∧
  twoLinesIntersectAtPoint xy l Z ∧
  P.onLine xy ∧ P ≠ Z ∧
  M.onCircle α ∧ N.onCircle β ∧
  distinctPointsOnLine A M am ∧
  distinctPointsOnLine D N dn
  →
  ∃ (Q : Point),
    Q.onLine am ∧
    Q.onLine dn ∧
    Q.onLine xy
:= by
  sorry

theorem problem_imo_2010_p2 :
∀ (A B C I D E F G X : Point) (AB BC CA : Line) (Γ : Circle),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  circumCircle Γ A B C ∧
  D.onCircle Γ ∧
  E.onCircle Γ ∧
  between B F C ∧
  ∠B:A:F = ∠C:A:E ∧
  (∠B:A:F + ∠C:A:E) < ∠B:A:C ∧
  midpoint I G F
  → X.onCircle Γ
:= by
  sorry


theorem problem_HP11 :
∀
(A B C D E P O : Point)
(Γ : Circle)
(PAB PC CD DB OP AC CE : Line),
----------------------------------------------------------------
  -- Circle-center setup and points on the circle
  O.isCentre Γ ∧
  A.onCircle Γ ∧
  B.onCircle Γ ∧
  C.onCircle Γ ∧
  D.onCircle Γ ∧

  -- “PAB is a secant”:  P,A,B are collinear
  threePointsOnLine P A B PAB ∧

  -- “PC is a tangent”:  P,C on line PC and that line is tangent to Γ
  distinctPointsOnLine P C PC ∧
  tangentLine PC Γ ∧

  -- “CD is a diameter”:  C,D on line CD and O is midpoint of segment CD
  distinctPointsOnLine C D CD ∧
  midpoint O C D ∧

  -- “Line DB intersects OP at E”
  distinctPointsOnLine D B DB ∧
  distinctPointsOnLine O P OP ∧
  twoLinesIntersectAtPoint DB OP E ∧

  -- Lines for the conclusion about perpendicularity
  distinctPointsOnLine A C AC ∧
  distinctPointsOnLine C E CE
----------------------------------------------------------------
→ perpLine AC CE
:= by
  sorry

theorem problem_MP34 :
∀ (A B C D : Point) (AB BC CA BD : Line),
  formTriangle A B C AB BC CA ∧
  (∠A:B:C = 45) ∧
  (∠B:C:A = 30) ∧
  distinctPointsOnLine B D BD ∧
  midpoint A D C
  → (∠A:B:D = 30)
:= by
  sorry

theorem problem_MP83 :
∀ (A B C D E F : Point)
  (AB BC CA AD BE : Line),
  formTriangle A B C AB BC CA ∧
  ∠A:B:C = ∟ ∧
  midpoint B D C ∧
  E.onLine AC ∧
  3 * |(A─E)| = |(A─C)| ∧
  distinctPointsOnLine A D AD ∧
  distinctPointsOnLine B E BE ∧
  twoLinesIntersectAtPoint AD BE F
  → ∠A:F:E = ∟
:= by
  sorry

theorem problem_HP35 :
∀ (A B C I E F N M D : Point) (AB BC CA MN AD : Line),
  formTriangle A B C AB BC CA ∧
  inCentre I A B C ∧
  midpoint B E C ∧
  midpoint B M I ∧
  midpoint E N F ∧
  distinctPointsOnLine M N MN ∧
  twoLinesIntersectAtPoint MN BC D ∧
  distinctPointsOnLine A D AD
→ inCentre M A B D := by
sorry

theorem problem_23G2 :
  ∀ (A B C P S D Q E : Point)
    (AB BC CA BP SP AE BE CQ DQ : Line)
    (ω : Circle)
    (r : Real),
  formTriangle A B C AB BC CA ∧
  (|(A─C)| > |(B─C)|) ∧
  circumCircle ω A B C ∧
  P.onLine CA ∧
  (|(B─C)| = |(C─P)|) ∧
  S.onLine AB ∧
  distinctPointsOnLine P S SP ∧
  perpLine SP AB ∧
  distinctPointsOnLine B P BP ∧
  D.onLine BP ∧
  D.onCircle ω ∧
  between B P D ∧
  threePointsOnLine S P Q SP ∧
  between S P Q ∧
  (|(P─Q)| = r) ∧
  distinctPointsOnLine A E AE ∧
  distinctPointsOnLine C Q CQ ∧
  perpLine AE CQ ∧
  distinctPointsOnLine B E BE ∧
  distinctPointsOnLine D Q DQ ∧
  perpLine BE DQ
  → E.onCircle ω :=
by
  sorry

theorem problem_12G7 :
∀ (A B C D E : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  (∃ X : Point, twoLinesIntersectAtPoint AD BC X)  ∧
  E.onLine BC ∧ between B E C ∧
  (∃ O₁ : Circle, tangentLine AB O₁ ∧ tangentLine BE O₁ ∧ tangentLine ED O₁ ∧ tangentLine DA O₁) ∧
  (∃ O₂ : Circle, tangentLine AE O₂ ∧ tangentLine EC O₂ ∧ tangentLine CF O₂ ∧ tangentLine FA O₂)
  →
  ( (∃ F : Point,
       F.onLine AD ∧ between A F D
       ∧ (∃ O₃ : Circle, tangentLine AB O₃ ∧ tangentLine BC O₃ ∧ tangentLine CF O₃ ∧ tangentLine FA O₃)
       ∧ (∃ O₄ : Circle, tangentLine BC O₄ ∧ tangentLine CD O₄ ∧ tangentLine DF O₄ ∧ tangentLine FB O₄)
     )
    ↔
    (¬ (∃ X : Point, twoLinesIntersectAtPoint AB CD X))
  )
:= by
  sorry

theorem problem_MP30 :
∀ (A B C D : Point) (AB BC CA AD : Line),
  (formTriangle A B C AB BC CA)
  ∧ D.onLine BC
  ∧ (∠ B:A:D = ∠ D:A:C)
  ∧ (|(A─C)| = |(A─B)| + |(B─D)|)
  ∧ (|(C─D)| = |(A─B)| + |(A─D)|)
  → (∠ B:A:C = 30) ∧ (∠ A:B:C = 60) ∧ (∠ A:C:B = ∟)
:= by
  sorry
