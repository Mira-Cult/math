import Sude.GeneratedTwinScan.S183C00
import Sude.GeneratedTwinScan.S183C01
import Sude.GeneratedTwinScan.S183C02
import Sude.GeneratedTwinScan.S183C03
import Sude.GeneratedTwinScan.S183C04
import Sude.GeneratedTwinScan.S183C05
import Sude.GeneratedTwinScan.S183C06
import Sude.GeneratedTwinScan.S183C07
import Sude.GeneratedTwinScan.S183C08
import Sude.GeneratedTwinScan.S183C09
import Sude.GeneratedTwinScan.S183C10
import Sude.GeneratedTwinScan.S183C11
import Sude.GeneratedTwinScan.S183C12
import Sude.GeneratedTwinScan.S183C13
import Sude.GeneratedTwinScan.S183C14
import Sude.GeneratedTwinScan.S183C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S183All

theorem join_0_0 : (twinPrimeSegment 383778861 384041005).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 383778861 ≤ 383909933)
    (by decide : 383909933 ≤ 384041005) S183C00.total S183C01.total

theorem join_0_1 : (twinPrimeSegment 384041005 384303149).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 384041005 ≤ 384172077)
    (by decide : 384172077 ≤ 384303149) S183C02.total S183C03.total

theorem join_0_2 : (twinPrimeSegment 384303149 384565293).card = 839 := by
  simpa using combineTwinPrimeSegments (by decide : 384303149 ≤ 384434221)
    (by decide : 384434221 ≤ 384565293) S183C04.total S183C05.total

theorem join_0_3 : (twinPrimeSegment 384565293 384827437).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 384565293 ≤ 384696365)
    (by decide : 384696365 ≤ 384827437) S183C06.total S183C07.total

theorem join_0_4 : (twinPrimeSegment 384827437 385089581).card = 857 := by
  simpa using combineTwinPrimeSegments (by decide : 384827437 ≤ 384958509)
    (by decide : 384958509 ≤ 385089581) S183C08.total S183C09.total

theorem join_0_5 : (twinPrimeSegment 385089581 385351725).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 385089581 ≤ 385220653)
    (by decide : 385220653 ≤ 385351725) S183C10.total S183C11.total

theorem join_0_6 : (twinPrimeSegment 385351725 385613869).card = 853 := by
  simpa using combineTwinPrimeSegments (by decide : 385351725 ≤ 385482797)
    (by decide : 385482797 ≤ 385613869) S183C12.total S183C13.total

theorem join_0_7 : (twinPrimeSegment 385613869 385876013).card = 880 := by
  simpa using combineTwinPrimeSegments (by decide : 385613869 ≤ 385744941)
    (by decide : 385744941 ≤ 385876013) S183C14.total S183C15.total

theorem join_1_0 : (twinPrimeSegment 383778861 384303149).card = 1794 := by
  simpa using combineTwinPrimeSegments (by decide : 383778861 ≤ 384041005)
    (by decide : 384041005 ≤ 384303149) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 384303149 384827437).card = 1758 := by
  simpa using combineTwinPrimeSegments (by decide : 384303149 ≤ 384565293)
    (by decide : 384565293 ≤ 384827437) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 384827437 385351725).card = 1771 := by
  simpa using combineTwinPrimeSegments (by decide : 384827437 ≤ 385089581)
    (by decide : 385089581 ≤ 385351725) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 385351725 385876013).card = 1733 := by
  simpa using combineTwinPrimeSegments (by decide : 385351725 ≤ 385613869)
    (by decide : 385613869 ≤ 385876013) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 383778861 384827437).card = 3552 := by
  simpa using combineTwinPrimeSegments (by decide : 383778861 ≤ 384303149)
    (by decide : 384303149 ≤ 384827437) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 384827437 385876013).card = 3504 := by
  simpa using combineTwinPrimeSegments (by decide : 384827437 ≤ 385351725)
    (by decide : 385351725 ≤ 385876013) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 383778861 385876013).card = 7056 := by
  simpa using combineTwinPrimeSegments (by decide : 383778861 ≤ 384827437)
    (by decide : 384827437 ≤ 385876013) join_2_0 join_2_1

theorem total : (twinPrimeSegment 383778861 385876013).card = 7056 := join_3_0

end S183All
end Sude.GeneratedTwinScan
