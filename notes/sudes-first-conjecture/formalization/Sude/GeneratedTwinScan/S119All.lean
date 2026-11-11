import Sude.GeneratedTwinScan.S119C00
import Sude.GeneratedTwinScan.S119C01
import Sude.GeneratedTwinScan.S119C02
import Sude.GeneratedTwinScan.S119C03
import Sude.GeneratedTwinScan.S119C04
import Sude.GeneratedTwinScan.S119C05
import Sude.GeneratedTwinScan.S119C06
import Sude.GeneratedTwinScan.S119C07
import Sude.GeneratedTwinScan.S119C08
import Sude.GeneratedTwinScan.S119C09
import Sude.GeneratedTwinScan.S119C10
import Sude.GeneratedTwinScan.S119C11
import Sude.GeneratedTwinScan.S119C12
import Sude.GeneratedTwinScan.S119C13
import Sude.GeneratedTwinScan.S119C14
import Sude.GeneratedTwinScan.S119C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S119All

theorem join_0_0 : (twinPrimeSegment 249561133 249823277).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 249561133 ≤ 249692205)
    (by decide : 249692205 ≤ 249823277) S119C00.total S119C01.total

theorem join_0_1 : (twinPrimeSegment 249823277 250085421).card = 899 := by
  simpa using combineTwinPrimeSegments (by decide : 249823277 ≤ 249954349)
    (by decide : 249954349 ≤ 250085421) S119C02.total S119C03.total

theorem join_0_2 : (twinPrimeSegment 250085421 250347565).card = 954 := by
  simpa using combineTwinPrimeSegments (by decide : 250085421 ≤ 250216493)
    (by decide : 250216493 ≤ 250347565) S119C04.total S119C05.total

theorem join_0_3 : (twinPrimeSegment 250347565 250609709).card = 939 := by
  simpa using combineTwinPrimeSegments (by decide : 250347565 ≤ 250478637)
    (by decide : 250478637 ≤ 250609709) S119C06.total S119C07.total

theorem join_0_4 : (twinPrimeSegment 250609709 250871853).card = 919 := by
  simpa using combineTwinPrimeSegments (by decide : 250609709 ≤ 250740781)
    (by decide : 250740781 ≤ 250871853) S119C08.total S119C09.total

theorem join_0_5 : (twinPrimeSegment 250871853 251133997).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 250871853 ≤ 251002925)
    (by decide : 251002925 ≤ 251133997) S119C10.total S119C11.total

theorem join_0_6 : (twinPrimeSegment 251133997 251396141).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 251133997 ≤ 251265069)
    (by decide : 251265069 ≤ 251396141) S119C12.total S119C13.total

theorem join_0_7 : (twinPrimeSegment 251396141 251658285).card = 932 := by
  simpa using combineTwinPrimeSegments (by decide : 251396141 ≤ 251527213)
    (by decide : 251527213 ≤ 251658285) S119C14.total S119C15.total

theorem join_1_0 : (twinPrimeSegment 249561133 250085421).card = 1808 := by
  simpa using combineTwinPrimeSegments (by decide : 249561133 ≤ 249823277)
    (by decide : 249823277 ≤ 250085421) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 250085421 250609709).card = 1893 := by
  simpa using combineTwinPrimeSegments (by decide : 250085421 ≤ 250347565)
    (by decide : 250347565 ≤ 250609709) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 250609709 251133997).card = 1817 := by
  simpa using combineTwinPrimeSegments (by decide : 250609709 ≤ 250871853)
    (by decide : 250871853 ≤ 251133997) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 251133997 251658285).card = 1855 := by
  simpa using combineTwinPrimeSegments (by decide : 251133997 ≤ 251396141)
    (by decide : 251396141 ≤ 251658285) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 249561133 250609709).card = 3701 := by
  simpa using combineTwinPrimeSegments (by decide : 249561133 ≤ 250085421)
    (by decide : 250085421 ≤ 250609709) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 250609709 251658285).card = 3672 := by
  simpa using combineTwinPrimeSegments (by decide : 250609709 ≤ 251133997)
    (by decide : 251133997 ≤ 251658285) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 249561133 251658285).card = 7373 := by
  simpa using combineTwinPrimeSegments (by decide : 249561133 ≤ 250609709)
    (by decide : 250609709 ≤ 251658285) join_2_0 join_2_1

theorem total : (twinPrimeSegment 249561133 251658285).card = 7373 := join_3_0

end S119All
end Sude.GeneratedTwinScan
