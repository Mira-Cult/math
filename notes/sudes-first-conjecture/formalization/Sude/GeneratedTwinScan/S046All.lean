import Sude.GeneratedTwinScan.S046C00
import Sude.GeneratedTwinScan.S046C01
import Sude.GeneratedTwinScan.S046C02
import Sude.GeneratedTwinScan.S046C03
import Sude.GeneratedTwinScan.S046C04
import Sude.GeneratedTwinScan.S046C05
import Sude.GeneratedTwinScan.S046C06
import Sude.GeneratedTwinScan.S046C07
import Sude.GeneratedTwinScan.S046C08
import Sude.GeneratedTwinScan.S046C09
import Sude.GeneratedTwinScan.S046C10
import Sude.GeneratedTwinScan.S046C11
import Sude.GeneratedTwinScan.S046C12
import Sude.GeneratedTwinScan.S046C13
import Sude.GeneratedTwinScan.S046C14
import Sude.GeneratedTwinScan.S046C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S046All

theorem join_0_0 : (twinPrimeSegment 96469037 96731181).card = 1006 := by
  simpa using combineTwinPrimeSegments (by decide : 96469037 ≤ 96600109)
    (by decide : 96600109 ≤ 96731181) S046C00.total S046C01.total

theorem join_0_1 : (twinPrimeSegment 96731181 96993325).card = 1016 := by
  simpa using combineTwinPrimeSegments (by decide : 96731181 ≤ 96862253)
    (by decide : 96862253 ≤ 96993325) S046C02.total S046C03.total

theorem join_0_2 : (twinPrimeSegment 96993325 97255469).card = 978 := by
  simpa using combineTwinPrimeSegments (by decide : 96993325 ≤ 97124397)
    (by decide : 97124397 ≤ 97255469) S046C04.total S046C05.total

theorem join_0_3 : (twinPrimeSegment 97255469 97517613).card = 1053 := by
  simpa using combineTwinPrimeSegments (by decide : 97255469 ≤ 97386541)
    (by decide : 97386541 ≤ 97517613) S046C06.total S046C07.total

theorem join_0_4 : (twinPrimeSegment 97517613 97779757).card = 1005 := by
  simpa using combineTwinPrimeSegments (by decide : 97517613 ≤ 97648685)
    (by decide : 97648685 ≤ 97779757) S046C08.total S046C09.total

theorem join_0_5 : (twinPrimeSegment 97779757 98041901).card = 1046 := by
  simpa using combineTwinPrimeSegments (by decide : 97779757 ≤ 97910829)
    (by decide : 97910829 ≤ 98041901) S046C10.total S046C11.total

theorem join_0_6 : (twinPrimeSegment 98041901 98304045).card = 1020 := by
  simpa using combineTwinPrimeSegments (by decide : 98041901 ≤ 98172973)
    (by decide : 98172973 ≤ 98304045) S046C12.total S046C13.total

theorem join_0_7 : (twinPrimeSegment 98304045 98566189).card = 1078 := by
  simpa using combineTwinPrimeSegments (by decide : 98304045 ≤ 98435117)
    (by decide : 98435117 ≤ 98566189) S046C14.total S046C15.total

theorem join_1_0 : (twinPrimeSegment 96469037 96993325).card = 2022 := by
  simpa using combineTwinPrimeSegments (by decide : 96469037 ≤ 96731181)
    (by decide : 96731181 ≤ 96993325) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 96993325 97517613).card = 2031 := by
  simpa using combineTwinPrimeSegments (by decide : 96993325 ≤ 97255469)
    (by decide : 97255469 ≤ 97517613) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 97517613 98041901).card = 2051 := by
  simpa using combineTwinPrimeSegments (by decide : 97517613 ≤ 97779757)
    (by decide : 97779757 ≤ 98041901) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 98041901 98566189).card = 2098 := by
  simpa using combineTwinPrimeSegments (by decide : 98041901 ≤ 98304045)
    (by decide : 98304045 ≤ 98566189) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 96469037 97517613).card = 4053 := by
  simpa using combineTwinPrimeSegments (by decide : 96469037 ≤ 96993325)
    (by decide : 96993325 ≤ 97517613) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 97517613 98566189).card = 4149 := by
  simpa using combineTwinPrimeSegments (by decide : 97517613 ≤ 98041901)
    (by decide : 98041901 ≤ 98566189) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 96469037 98566189).card = 8202 := by
  simpa using combineTwinPrimeSegments (by decide : 96469037 ≤ 97517613)
    (by decide : 97517613 ≤ 98566189) join_2_0 join_2_1

theorem total : (twinPrimeSegment 96469037 98566189).card = 8202 := join_3_0

end S046All
end Sude.GeneratedTwinScan
