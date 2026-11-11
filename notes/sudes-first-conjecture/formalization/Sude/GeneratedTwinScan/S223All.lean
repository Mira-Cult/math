import Sude.GeneratedTwinScan.S223C00
import Sude.GeneratedTwinScan.S223C01
import Sude.GeneratedTwinScan.S223C02
import Sude.GeneratedTwinScan.S223C03
import Sude.GeneratedTwinScan.S223C04
import Sude.GeneratedTwinScan.S223C05
import Sude.GeneratedTwinScan.S223C06
import Sude.GeneratedTwinScan.S223C07
import Sude.GeneratedTwinScan.S223C08
import Sude.GeneratedTwinScan.S223C09
import Sude.GeneratedTwinScan.S223C10
import Sude.GeneratedTwinScan.S223C11
import Sude.GeneratedTwinScan.S223C12
import Sude.GeneratedTwinScan.S223C13
import Sude.GeneratedTwinScan.S223C14
import Sude.GeneratedTwinScan.S223C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S223All

theorem join_0_0 : (twinPrimeSegment 467664941 467927085).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 467664941 ≤ 467796013)
    (by decide : 467796013 ≤ 467927085) S223C00.total S223C01.total

theorem join_0_1 : (twinPrimeSegment 467927085 468189229).card = 844 := by
  simpa using combineTwinPrimeSegments (by decide : 467927085 ≤ 468058157)
    (by decide : 468058157 ≤ 468189229) S223C02.total S223C03.total

theorem join_0_2 : (twinPrimeSegment 468189229 468451373).card = 824 := by
  simpa using combineTwinPrimeSegments (by decide : 468189229 ≤ 468320301)
    (by decide : 468320301 ≤ 468451373) S223C04.total S223C05.total

theorem join_0_3 : (twinPrimeSegment 468451373 468713517).card = 861 := by
  simpa using combineTwinPrimeSegments (by decide : 468451373 ≤ 468582445)
    (by decide : 468582445 ≤ 468713517) S223C06.total S223C07.total

theorem join_0_4 : (twinPrimeSegment 468713517 468975661).card = 838 := by
  simpa using combineTwinPrimeSegments (by decide : 468713517 ≤ 468844589)
    (by decide : 468844589 ≤ 468975661) S223C08.total S223C09.total

theorem join_0_5 : (twinPrimeSegment 468975661 469237805).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 468975661 ≤ 469106733)
    (by decide : 469106733 ≤ 469237805) S223C10.total S223C11.total

theorem join_0_6 : (twinPrimeSegment 469237805 469499949).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 469237805 ≤ 469368877)
    (by decide : 469368877 ≤ 469499949) S223C12.total S223C13.total

theorem join_0_7 : (twinPrimeSegment 469499949 469762093).card = 866 := by
  simpa using combineTwinPrimeSegments (by decide : 469499949 ≤ 469631021)
    (by decide : 469631021 ≤ 469762093) S223C14.total S223C15.total

theorem join_1_0 : (twinPrimeSegment 467664941 468189229).card = 1731 := by
  simpa using combineTwinPrimeSegments (by decide : 467664941 ≤ 467927085)
    (by decide : 467927085 ≤ 468189229) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 468189229 468713517).card = 1685 := by
  simpa using combineTwinPrimeSegments (by decide : 468189229 ≤ 468451373)
    (by decide : 468451373 ≤ 468713517) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 468713517 469237805).card = 1674 := by
  simpa using combineTwinPrimeSegments (by decide : 468713517 ≤ 468975661)
    (by decide : 468975661 ≤ 469237805) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 469237805 469762093).card = 1736 := by
  simpa using combineTwinPrimeSegments (by decide : 469237805 ≤ 469499949)
    (by decide : 469499949 ≤ 469762093) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 467664941 468713517).card = 3416 := by
  simpa using combineTwinPrimeSegments (by decide : 467664941 ≤ 468189229)
    (by decide : 468189229 ≤ 468713517) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 468713517 469762093).card = 3410 := by
  simpa using combineTwinPrimeSegments (by decide : 468713517 ≤ 469237805)
    (by decide : 469237805 ≤ 469762093) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 467664941 469762093).card = 6826 := by
  simpa using combineTwinPrimeSegments (by decide : 467664941 ≤ 468713517)
    (by decide : 468713517 ≤ 469762093) join_2_0 join_2_1

theorem total : (twinPrimeSegment 467664941 469762093).card = 6826 := join_3_0

end S223All
end Sude.GeneratedTwinScan
