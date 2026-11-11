import Sude.GeneratedTwinScan.S042C00
import Sude.GeneratedTwinScan.S042C01
import Sude.GeneratedTwinScan.S042C02
import Sude.GeneratedTwinScan.S042C03
import Sude.GeneratedTwinScan.S042C04
import Sude.GeneratedTwinScan.S042C05
import Sude.GeneratedTwinScan.S042C06
import Sude.GeneratedTwinScan.S042C07
import Sude.GeneratedTwinScan.S042C08
import Sude.GeneratedTwinScan.S042C09
import Sude.GeneratedTwinScan.S042C10
import Sude.GeneratedTwinScan.S042C11
import Sude.GeneratedTwinScan.S042C12
import Sude.GeneratedTwinScan.S042C13
import Sude.GeneratedTwinScan.S042C14
import Sude.GeneratedTwinScan.S042C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S042All

theorem join_0_0 : (twinPrimeSegment 88080429 88342573).card = 1045 := by
  simpa using combineTwinPrimeSegments (by decide : 88080429 ≤ 88211501)
    (by decide : 88211501 ≤ 88342573) S042C00.total S042C01.total

theorem join_0_1 : (twinPrimeSegment 88342573 88604717).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 88342573 ≤ 88473645)
    (by decide : 88473645 ≤ 88604717) S042C02.total S042C03.total

theorem join_0_2 : (twinPrimeSegment 88604717 88866861).card = 1056 := by
  simpa using combineTwinPrimeSegments (by decide : 88604717 ≤ 88735789)
    (by decide : 88735789 ≤ 88866861) S042C04.total S042C05.total

theorem join_0_3 : (twinPrimeSegment 88866861 89129005).card = 1080 := by
  simpa using combineTwinPrimeSegments (by decide : 88866861 ≤ 88997933)
    (by decide : 88997933 ≤ 89129005) S042C06.total S042C07.total

theorem join_0_4 : (twinPrimeSegment 89129005 89391149).card = 1025 := by
  simpa using combineTwinPrimeSegments (by decide : 89129005 ≤ 89260077)
    (by decide : 89260077 ≤ 89391149) S042C08.total S042C09.total

theorem join_0_5 : (twinPrimeSegment 89391149 89653293).card = 984 := by
  simpa using combineTwinPrimeSegments (by decide : 89391149 ≤ 89522221)
    (by decide : 89522221 ≤ 89653293) S042C10.total S042C11.total

theorem join_0_6 : (twinPrimeSegment 89653293 89915437).card = 1048 := by
  simpa using combineTwinPrimeSegments (by decide : 89653293 ≤ 89784365)
    (by decide : 89784365 ≤ 89915437) S042C12.total S042C13.total

theorem join_0_7 : (twinPrimeSegment 89915437 90177581).card = 1031 := by
  simpa using combineTwinPrimeSegments (by decide : 89915437 ≤ 90046509)
    (by decide : 90046509 ≤ 90177581) S042C14.total S042C15.total

theorem join_1_0 : (twinPrimeSegment 88080429 88604717).card = 2015 := by
  simpa using combineTwinPrimeSegments (by decide : 88080429 ≤ 88342573)
    (by decide : 88342573 ≤ 88604717) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 88604717 89129005).card = 2136 := by
  simpa using combineTwinPrimeSegments (by decide : 88604717 ≤ 88866861)
    (by decide : 88866861 ≤ 89129005) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 89129005 89653293).card = 2009 := by
  simpa using combineTwinPrimeSegments (by decide : 89129005 ≤ 89391149)
    (by decide : 89391149 ≤ 89653293) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 89653293 90177581).card = 2079 := by
  simpa using combineTwinPrimeSegments (by decide : 89653293 ≤ 89915437)
    (by decide : 89915437 ≤ 90177581) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 88080429 89129005).card = 4151 := by
  simpa using combineTwinPrimeSegments (by decide : 88080429 ≤ 88604717)
    (by decide : 88604717 ≤ 89129005) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 89129005 90177581).card = 4088 := by
  simpa using combineTwinPrimeSegments (by decide : 89129005 ≤ 89653293)
    (by decide : 89653293 ≤ 90177581) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 88080429 90177581).card = 8239 := by
  simpa using combineTwinPrimeSegments (by decide : 88080429 ≤ 89129005)
    (by decide : 89129005 ≤ 90177581) join_2_0 join_2_1

theorem total : (twinPrimeSegment 88080429 90177581).card = 8239 := join_3_0

end S042All
end Sude.GeneratedTwinScan
