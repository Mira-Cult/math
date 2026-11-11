import Sude.GeneratedTwinScan.S098C00
import Sude.GeneratedTwinScan.S098C01
import Sude.GeneratedTwinScan.S098C02
import Sude.GeneratedTwinScan.S098C03
import Sude.GeneratedTwinScan.S098C04
import Sude.GeneratedTwinScan.S098C05
import Sude.GeneratedTwinScan.S098C06
import Sude.GeneratedTwinScan.S098C07
import Sude.GeneratedTwinScan.S098C08
import Sude.GeneratedTwinScan.S098C09
import Sude.GeneratedTwinScan.S098C10
import Sude.GeneratedTwinScan.S098C11
import Sude.GeneratedTwinScan.S098C12
import Sude.GeneratedTwinScan.S098C13
import Sude.GeneratedTwinScan.S098C14
import Sude.GeneratedTwinScan.S098C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S098All

theorem join_0_0 : (twinPrimeSegment 205520941 205783085).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 205520941 ≤ 205652013)
    (by decide : 205652013 ≤ 205783085) S098C00.total S098C01.total

theorem join_0_1 : (twinPrimeSegment 205783085 206045229).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 205783085 ≤ 205914157)
    (by decide : 205914157 ≤ 206045229) S098C02.total S098C03.total

theorem join_0_2 : (twinPrimeSegment 206045229 206307373).card = 988 := by
  simpa using combineTwinPrimeSegments (by decide : 206045229 ≤ 206176301)
    (by decide : 206176301 ≤ 206307373) S098C04.total S098C05.total

theorem join_0_3 : (twinPrimeSegment 206307373 206569517).card = 956 := by
  simpa using combineTwinPrimeSegments (by decide : 206307373 ≤ 206438445)
    (by decide : 206438445 ≤ 206569517) S098C06.total S098C07.total

theorem join_0_4 : (twinPrimeSegment 206569517 206831661).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 206569517 ≤ 206700589)
    (by decide : 206700589 ≤ 206831661) S098C08.total S098C09.total

theorem join_0_5 : (twinPrimeSegment 206831661 207093805).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 206831661 ≤ 206962733)
    (by decide : 206962733 ≤ 207093805) S098C10.total S098C11.total

theorem join_0_6 : (twinPrimeSegment 207093805 207355949).card = 936 := by
  simpa using combineTwinPrimeSegments (by decide : 207093805 ≤ 207224877)
    (by decide : 207224877 ≤ 207355949) S098C12.total S098C13.total

theorem join_0_7 : (twinPrimeSegment 207355949 207618093).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 207355949 ≤ 207487021)
    (by decide : 207487021 ≤ 207618093) S098C14.total S098C15.total

theorem join_1_0 : (twinPrimeSegment 205520941 206045229).card = 1835 := by
  simpa using combineTwinPrimeSegments (by decide : 205520941 ≤ 205783085)
    (by decide : 205783085 ≤ 206045229) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 206045229 206569517).card = 1944 := by
  simpa using combineTwinPrimeSegments (by decide : 206045229 ≤ 206307373)
    (by decide : 206307373 ≤ 206569517) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 206569517 207093805).card = 1878 := by
  simpa using combineTwinPrimeSegments (by decide : 206569517 ≤ 206831661)
    (by decide : 206831661 ≤ 207093805) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 207093805 207618093).card = 1874 := by
  simpa using combineTwinPrimeSegments (by decide : 207093805 ≤ 207355949)
    (by decide : 207355949 ≤ 207618093) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 205520941 206569517).card = 3779 := by
  simpa using combineTwinPrimeSegments (by decide : 205520941 ≤ 206045229)
    (by decide : 206045229 ≤ 206569517) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 206569517 207618093).card = 3752 := by
  simpa using combineTwinPrimeSegments (by decide : 206569517 ≤ 207093805)
    (by decide : 207093805 ≤ 207618093) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 205520941 207618093).card = 7531 := by
  simpa using combineTwinPrimeSegments (by decide : 205520941 ≤ 206569517)
    (by decide : 206569517 ≤ 207618093) join_2_0 join_2_1

theorem total : (twinPrimeSegment 205520941 207618093).card = 7531 := join_3_0

end S098All
end Sude.GeneratedTwinScan
