import Sude.GeneratedTwinScan.S124C00
import Sude.GeneratedTwinScan.S124C01
import Sude.GeneratedTwinScan.S124C02
import Sude.GeneratedTwinScan.S124C03
import Sude.GeneratedTwinScan.S124C04
import Sude.GeneratedTwinScan.S124C05
import Sude.GeneratedTwinScan.S124C06
import Sude.GeneratedTwinScan.S124C07
import Sude.GeneratedTwinScan.S124C08
import Sude.GeneratedTwinScan.S124C09
import Sude.GeneratedTwinScan.S124C10
import Sude.GeneratedTwinScan.S124C11
import Sude.GeneratedTwinScan.S124C12
import Sude.GeneratedTwinScan.S124C13
import Sude.GeneratedTwinScan.S124C14
import Sude.GeneratedTwinScan.S124C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S124All

theorem join_0_0 : (twinPrimeSegment 260046893 260309037).card = 906 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 260177965)
    (by decide : 260177965 ≤ 260309037) S124C00.total S124C01.total

theorem join_0_1 : (twinPrimeSegment 260309037 260571181).card = 942 := by
  simpa using combineTwinPrimeSegments (by decide : 260309037 ≤ 260440109)
    (by decide : 260440109 ≤ 260571181) S124C02.total S124C03.total

theorem join_0_2 : (twinPrimeSegment 260571181 260833325).card = 937 := by
  simpa using combineTwinPrimeSegments (by decide : 260571181 ≤ 260702253)
    (by decide : 260702253 ≤ 260833325) S124C04.total S124C05.total

theorem join_0_3 : (twinPrimeSegment 260833325 261095469).card = 984 := by
  simpa using combineTwinPrimeSegments (by decide : 260833325 ≤ 260964397)
    (by decide : 260964397 ≤ 261095469) S124C06.total S124C07.total

theorem join_0_4 : (twinPrimeSegment 261095469 261357613).card = 926 := by
  simpa using combineTwinPrimeSegments (by decide : 261095469 ≤ 261226541)
    (by decide : 261226541 ≤ 261357613) S124C08.total S124C09.total

theorem join_0_5 : (twinPrimeSegment 261357613 261619757).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 261357613 ≤ 261488685)
    (by decide : 261488685 ≤ 261619757) S124C10.total S124C11.total

theorem join_0_6 : (twinPrimeSegment 261619757 261881901).card = 926 := by
  simpa using combineTwinPrimeSegments (by decide : 261619757 ≤ 261750829)
    (by decide : 261750829 ≤ 261881901) S124C12.total S124C13.total

theorem join_0_7 : (twinPrimeSegment 261881901 262144045).card = 1010 := by
  simpa using combineTwinPrimeSegments (by decide : 261881901 ≤ 262012973)
    (by decide : 262012973 ≤ 262144045) S124C14.total S124C15.total

theorem join_1_0 : (twinPrimeSegment 260046893 260571181).card = 1848 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 260309037)
    (by decide : 260309037 ≤ 260571181) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 260571181 261095469).card = 1921 := by
  simpa using combineTwinPrimeSegments (by decide : 260571181 ≤ 260833325)
    (by decide : 260833325 ≤ 261095469) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 261095469 261619757).card = 1870 := by
  simpa using combineTwinPrimeSegments (by decide : 261095469 ≤ 261357613)
    (by decide : 261357613 ≤ 261619757) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 261619757 262144045).card = 1936 := by
  simpa using combineTwinPrimeSegments (by decide : 261619757 ≤ 261881901)
    (by decide : 261881901 ≤ 262144045) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 260046893 261095469).card = 3769 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 260571181)
    (by decide : 260571181 ≤ 261095469) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 261095469 262144045).card = 3806 := by
  simpa using combineTwinPrimeSegments (by decide : 261095469 ≤ 261619757)
    (by decide : 261619757 ≤ 262144045) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 260046893 262144045).card = 7575 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 261095469)
    (by decide : 261095469 ≤ 262144045) join_2_0 join_2_1

theorem total : (twinPrimeSegment 260046893 262144045).card = 7575 := join_3_0

end S124All
end Sude.GeneratedTwinScan
