import Sude.GeneratedTwinScan.S112C00
import Sude.GeneratedTwinScan.S112C01
import Sude.GeneratedTwinScan.S112C02
import Sude.GeneratedTwinScan.S112C03
import Sude.GeneratedTwinScan.S112C04
import Sude.GeneratedTwinScan.S112C05
import Sude.GeneratedTwinScan.S112C06
import Sude.GeneratedTwinScan.S112C07
import Sude.GeneratedTwinScan.S112C08
import Sude.GeneratedTwinScan.S112C09
import Sude.GeneratedTwinScan.S112C10
import Sude.GeneratedTwinScan.S112C11
import Sude.GeneratedTwinScan.S112C12
import Sude.GeneratedTwinScan.S112C13
import Sude.GeneratedTwinScan.S112C14
import Sude.GeneratedTwinScan.S112C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S112All

theorem join_0_0 : (twinPrimeSegment 234881069 235143213).card = 935 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 235012141)
    (by decide : 235012141 ≤ 235143213) S112C00.total S112C01.total

theorem join_0_1 : (twinPrimeSegment 235143213 235405357).card = 970 := by
  simpa using combineTwinPrimeSegments (by decide : 235143213 ≤ 235274285)
    (by decide : 235274285 ≤ 235405357) S112C02.total S112C03.total

theorem join_0_2 : (twinPrimeSegment 235405357 235667501).card = 921 := by
  simpa using combineTwinPrimeSegments (by decide : 235405357 ≤ 235536429)
    (by decide : 235536429 ≤ 235667501) S112C04.total S112C05.total

theorem join_0_3 : (twinPrimeSegment 235667501 235929645).card = 933 := by
  simpa using combineTwinPrimeSegments (by decide : 235667501 ≤ 235798573)
    (by decide : 235798573 ≤ 235929645) S112C06.total S112C07.total

theorem join_0_4 : (twinPrimeSegment 235929645 236191789).card = 969 := by
  simpa using combineTwinPrimeSegments (by decide : 235929645 ≤ 236060717)
    (by decide : 236060717 ≤ 236191789) S112C08.total S112C09.total

theorem join_0_5 : (twinPrimeSegment 236191789 236453933).card = 967 := by
  simpa using combineTwinPrimeSegments (by decide : 236191789 ≤ 236322861)
    (by decide : 236322861 ≤ 236453933) S112C10.total S112C11.total

theorem join_0_6 : (twinPrimeSegment 236453933 236716077).card = 959 := by
  simpa using combineTwinPrimeSegments (by decide : 236453933 ≤ 236585005)
    (by decide : 236585005 ≤ 236716077) S112C12.total S112C13.total

theorem join_0_7 : (twinPrimeSegment 236716077 236978221).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 236716077 ≤ 236847149)
    (by decide : 236847149 ≤ 236978221) S112C14.total S112C15.total

theorem join_1_0 : (twinPrimeSegment 234881069 235405357).card = 1905 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 235143213)
    (by decide : 235143213 ≤ 235405357) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 235405357 235929645).card = 1854 := by
  simpa using combineTwinPrimeSegments (by decide : 235405357 ≤ 235667501)
    (by decide : 235667501 ≤ 235929645) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 235929645 236453933).card = 1936 := by
  simpa using combineTwinPrimeSegments (by decide : 235929645 ≤ 236191789)
    (by decide : 236191789 ≤ 236453933) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 236453933 236978221).card = 1878 := by
  simpa using combineTwinPrimeSegments (by decide : 236453933 ≤ 236716077)
    (by decide : 236716077 ≤ 236978221) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 234881069 235929645).card = 3759 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 235405357)
    (by decide : 235405357 ≤ 235929645) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 235929645 236978221).card = 3814 := by
  simpa using combineTwinPrimeSegments (by decide : 235929645 ≤ 236453933)
    (by decide : 236453933 ≤ 236978221) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 234881069 236978221).card = 7573 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 235929645)
    (by decide : 235929645 ≤ 236978221) join_2_0 join_2_1

theorem total : (twinPrimeSegment 234881069 236978221).card = 7573 := join_3_0

end S112All
end Sude.GeneratedTwinScan
