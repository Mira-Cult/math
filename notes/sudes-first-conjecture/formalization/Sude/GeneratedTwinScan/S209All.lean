import Sude.GeneratedTwinScan.S209C00
import Sude.GeneratedTwinScan.S209C01
import Sude.GeneratedTwinScan.S209C02
import Sude.GeneratedTwinScan.S209C03
import Sude.GeneratedTwinScan.S209C04
import Sude.GeneratedTwinScan.S209C05
import Sude.GeneratedTwinScan.S209C06
import Sude.GeneratedTwinScan.S209C07
import Sude.GeneratedTwinScan.S209C08
import Sude.GeneratedTwinScan.S209C09
import Sude.GeneratedTwinScan.S209C10
import Sude.GeneratedTwinScan.S209C11
import Sude.GeneratedTwinScan.S209C12
import Sude.GeneratedTwinScan.S209C13
import Sude.GeneratedTwinScan.S209C14
import Sude.GeneratedTwinScan.S209C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S209All

theorem join_0_0 : (twinPrimeSegment 438304813 438566957).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 438304813 ≤ 438435885)
    (by decide : 438435885 ≤ 438566957) S209C00.total S209C01.total

theorem join_0_1 : (twinPrimeSegment 438566957 438829101).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 438566957 ≤ 438698029)
    (by decide : 438698029 ≤ 438829101) S209C02.total S209C03.total

theorem join_0_2 : (twinPrimeSegment 438829101 439091245).card = 859 := by
  simpa using combineTwinPrimeSegments (by decide : 438829101 ≤ 438960173)
    (by decide : 438960173 ≤ 439091245) S209C04.total S209C05.total

theorem join_0_3 : (twinPrimeSegment 439091245 439353389).card = 872 := by
  simpa using combineTwinPrimeSegments (by decide : 439091245 ≤ 439222317)
    (by decide : 439222317 ≤ 439353389) S209C06.total S209C07.total

theorem join_0_4 : (twinPrimeSegment 439353389 439615533).card = 860 := by
  simpa using combineTwinPrimeSegments (by decide : 439353389 ≤ 439484461)
    (by decide : 439484461 ≤ 439615533) S209C08.total S209C09.total

theorem join_0_5 : (twinPrimeSegment 439615533 439877677).card = 855 := by
  simpa using combineTwinPrimeSegments (by decide : 439615533 ≤ 439746605)
    (by decide : 439746605 ≤ 439877677) S209C10.total S209C11.total

theorem join_0_6 : (twinPrimeSegment 439877677 440139821).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 439877677 ≤ 440008749)
    (by decide : 440008749 ≤ 440139821) S209C12.total S209C13.total

theorem join_0_7 : (twinPrimeSegment 440139821 440401965).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 440139821 ≤ 440270893)
    (by decide : 440270893 ≤ 440401965) S209C14.total S209C15.total

theorem join_1_0 : (twinPrimeSegment 438304813 438829101).card = 1857 := by
  simpa using combineTwinPrimeSegments (by decide : 438304813 ≤ 438566957)
    (by decide : 438566957 ≤ 438829101) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 438829101 439353389).card = 1731 := by
  simpa using combineTwinPrimeSegments (by decide : 438829101 ≤ 439091245)
    (by decide : 439091245 ≤ 439353389) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 439353389 439877677).card = 1715 := by
  simpa using combineTwinPrimeSegments (by decide : 439353389 ≤ 439615533)
    (by decide : 439615533 ≤ 439877677) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 439877677 440401965).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 439877677 ≤ 440139821)
    (by decide : 440139821 ≤ 440401965) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 438304813 439353389).card = 3588 := by
  simpa using combineTwinPrimeSegments (by decide : 438304813 ≤ 438829101)
    (by decide : 438829101 ≤ 439353389) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 439353389 440401965).card = 3450 := by
  simpa using combineTwinPrimeSegments (by decide : 439353389 ≤ 439877677)
    (by decide : 439877677 ≤ 440401965) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 438304813 440401965).card = 7038 := by
  simpa using combineTwinPrimeSegments (by decide : 438304813 ≤ 439353389)
    (by decide : 439353389 ≤ 440401965) join_2_0 join_2_1

theorem total : (twinPrimeSegment 438304813 440401965).card = 7038 := join_3_0

end S209All
end Sude.GeneratedTwinScan
