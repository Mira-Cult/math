import Sude.GeneratedTwinScan.S104C00
import Sude.GeneratedTwinScan.S104C01
import Sude.GeneratedTwinScan.S104C02
import Sude.GeneratedTwinScan.S104C03
import Sude.GeneratedTwinScan.S104C04
import Sude.GeneratedTwinScan.S104C05
import Sude.GeneratedTwinScan.S104C06
import Sude.GeneratedTwinScan.S104C07
import Sude.GeneratedTwinScan.S104C08
import Sude.GeneratedTwinScan.S104C09
import Sude.GeneratedTwinScan.S104C10
import Sude.GeneratedTwinScan.S104C11
import Sude.GeneratedTwinScan.S104C12
import Sude.GeneratedTwinScan.S104C13
import Sude.GeneratedTwinScan.S104C14
import Sude.GeneratedTwinScan.S104C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S104All

theorem join_0_0 : (twinPrimeSegment 218103853 218365997).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 218234925)
    (by decide : 218234925 ≤ 218365997) S104C00.total S104C01.total

theorem join_0_1 : (twinPrimeSegment 218365997 218628141).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 218365997 ≤ 218497069)
    (by decide : 218497069 ≤ 218628141) S104C02.total S104C03.total

theorem join_0_2 : (twinPrimeSegment 218628141 218890285).card = 955 := by
  simpa using combineTwinPrimeSegments (by decide : 218628141 ≤ 218759213)
    (by decide : 218759213 ≤ 218890285) S104C04.total S104C05.total

theorem join_0_3 : (twinPrimeSegment 218890285 219152429).card = 907 := by
  simpa using combineTwinPrimeSegments (by decide : 218890285 ≤ 219021357)
    (by decide : 219021357 ≤ 219152429) S104C06.total S104C07.total

theorem join_0_4 : (twinPrimeSegment 219152429 219414573).card = 943 := by
  simpa using combineTwinPrimeSegments (by decide : 219152429 ≤ 219283501)
    (by decide : 219283501 ≤ 219414573) S104C08.total S104C09.total

theorem join_0_5 : (twinPrimeSegment 219414573 219676717).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 219414573 ≤ 219545645)
    (by decide : 219545645 ≤ 219676717) S104C10.total S104C11.total

theorem join_0_6 : (twinPrimeSegment 219676717 219938861).card = 938 := by
  simpa using combineTwinPrimeSegments (by decide : 219676717 ≤ 219807789)
    (by decide : 219807789 ≤ 219938861) S104C12.total S104C13.total

theorem join_0_7 : (twinPrimeSegment 219938861 220201005).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 219938861 ≤ 220069933)
    (by decide : 220069933 ≤ 220201005) S104C14.total S104C15.total

theorem join_1_0 : (twinPrimeSegment 218103853 218628141).card = 1836 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 218365997)
    (by decide : 218365997 ≤ 218628141) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 218628141 219152429).card = 1862 := by
  simpa using combineTwinPrimeSegments (by decide : 218628141 ≤ 218890285)
    (by decide : 218890285 ≤ 219152429) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 219152429 219676717).card = 1834 := by
  simpa using combineTwinPrimeSegments (by decide : 219152429 ≤ 219414573)
    (by decide : 219414573 ≤ 219676717) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 219676717 220201005).card = 1880 := by
  simpa using combineTwinPrimeSegments (by decide : 219676717 ≤ 219938861)
    (by decide : 219938861 ≤ 220201005) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 218103853 219152429).card = 3698 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 218628141)
    (by decide : 218628141 ≤ 219152429) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 219152429 220201005).card = 3714 := by
  simpa using combineTwinPrimeSegments (by decide : 219152429 ≤ 219676717)
    (by decide : 219676717 ≤ 220201005) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 218103853 220201005).card = 7412 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 219152429)
    (by decide : 219152429 ≤ 220201005) join_2_0 join_2_1

theorem total : (twinPrimeSegment 218103853 220201005).card = 7412 := join_3_0

end S104All
end Sude.GeneratedTwinScan
