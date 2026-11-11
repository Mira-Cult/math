import Sude.GeneratedTwinScan.S127C00
import Sude.GeneratedTwinScan.S127C01
import Sude.GeneratedTwinScan.S127C02
import Sude.GeneratedTwinScan.S127C03
import Sude.GeneratedTwinScan.S127C04
import Sude.GeneratedTwinScan.S127C05
import Sude.GeneratedTwinScan.S127C06
import Sude.GeneratedTwinScan.S127C07
import Sude.GeneratedTwinScan.S127C08
import Sude.GeneratedTwinScan.S127C09
import Sude.GeneratedTwinScan.S127C10
import Sude.GeneratedTwinScan.S127C11
import Sude.GeneratedTwinScan.S127C12
import Sude.GeneratedTwinScan.S127C13
import Sude.GeneratedTwinScan.S127C14
import Sude.GeneratedTwinScan.S127C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S127All

theorem join_0_0 : (twinPrimeSegment 266338349 266600493).card = 883 := by
  simpa using combineTwinPrimeSegments (by decide : 266338349 ≤ 266469421)
    (by decide : 266469421 ≤ 266600493) S127C00.total S127C01.total

theorem join_0_1 : (twinPrimeSegment 266600493 266862637).card = 902 := by
  simpa using combineTwinPrimeSegments (by decide : 266600493 ≤ 266731565)
    (by decide : 266731565 ≤ 266862637) S127C02.total S127C03.total

theorem join_0_2 : (twinPrimeSegment 266862637 267124781).card = 900 := by
  simpa using combineTwinPrimeSegments (by decide : 266862637 ≤ 266993709)
    (by decide : 266993709 ≤ 267124781) S127C04.total S127C05.total

theorem join_0_3 : (twinPrimeSegment 267124781 267386925).card = 952 := by
  simpa using combineTwinPrimeSegments (by decide : 267124781 ≤ 267255853)
    (by decide : 267255853 ≤ 267386925) S127C06.total S127C07.total

theorem join_0_4 : (twinPrimeSegment 267386925 267649069).card = 836 := by
  simpa using combineTwinPrimeSegments (by decide : 267386925 ≤ 267517997)
    (by decide : 267517997 ≤ 267649069) S127C08.total S127C09.total

theorem join_0_5 : (twinPrimeSegment 267649069 267911213).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 267649069 ≤ 267780141)
    (by decide : 267780141 ≤ 267911213) S127C10.total S127C11.total

theorem join_0_6 : (twinPrimeSegment 267911213 268173357).card = 927 := by
  simpa using combineTwinPrimeSegments (by decide : 267911213 ≤ 268042285)
    (by decide : 268042285 ≤ 268173357) S127C12.total S127C13.total

theorem join_0_7 : (twinPrimeSegment 268173357 268435501).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 268173357 ≤ 268304429)
    (by decide : 268304429 ≤ 268435501) S127C14.total S127C15.total

theorem join_1_0 : (twinPrimeSegment 266338349 266862637).card = 1785 := by
  simpa using combineTwinPrimeSegments (by decide : 266338349 ≤ 266600493)
    (by decide : 266600493 ≤ 266862637) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 266862637 267386925).card = 1852 := by
  simpa using combineTwinPrimeSegments (by decide : 266862637 ≤ 267124781)
    (by decide : 267124781 ≤ 267386925) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 267386925 267911213).card = 1746 := by
  simpa using combineTwinPrimeSegments (by decide : 267386925 ≤ 267649069)
    (by decide : 267649069 ≤ 267911213) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 267911213 268435501).card = 1840 := by
  simpa using combineTwinPrimeSegments (by decide : 267911213 ≤ 268173357)
    (by decide : 268173357 ≤ 268435501) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 266338349 267386925).card = 3637 := by
  simpa using combineTwinPrimeSegments (by decide : 266338349 ≤ 266862637)
    (by decide : 266862637 ≤ 267386925) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 267386925 268435501).card = 3586 := by
  simpa using combineTwinPrimeSegments (by decide : 267386925 ≤ 267911213)
    (by decide : 267911213 ≤ 268435501) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 266338349 268435501).card = 7223 := by
  simpa using combineTwinPrimeSegments (by decide : 266338349 ≤ 267386925)
    (by decide : 267386925 ≤ 268435501) join_2_0 join_2_1

theorem total : (twinPrimeSegment 266338349 268435501).card = 7223 := join_3_0

end S127All
end Sude.GeneratedTwinScan
