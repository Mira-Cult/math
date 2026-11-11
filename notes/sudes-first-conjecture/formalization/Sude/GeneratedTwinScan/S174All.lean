import Sude.GeneratedTwinScan.S174C00
import Sude.GeneratedTwinScan.S174C01
import Sude.GeneratedTwinScan.S174C02
import Sude.GeneratedTwinScan.S174C03
import Sude.GeneratedTwinScan.S174C04
import Sude.GeneratedTwinScan.S174C05
import Sude.GeneratedTwinScan.S174C06
import Sude.GeneratedTwinScan.S174C07
import Sude.GeneratedTwinScan.S174C08
import Sude.GeneratedTwinScan.S174C09
import Sude.GeneratedTwinScan.S174C10
import Sude.GeneratedTwinScan.S174C11
import Sude.GeneratedTwinScan.S174C12
import Sude.GeneratedTwinScan.S174C13
import Sude.GeneratedTwinScan.S174C14
import Sude.GeneratedTwinScan.S174C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S174All

theorem join_0_0 : (twinPrimeSegment 364904493 365166637).card = 909 := by
  simpa using combineTwinPrimeSegments (by decide : 364904493 ≤ 365035565)
    (by decide : 365035565 ≤ 365166637) S174C00.total S174C01.total

theorem join_0_1 : (twinPrimeSegment 365166637 365428781).card = 878 := by
  simpa using combineTwinPrimeSegments (by decide : 365166637 ≤ 365297709)
    (by decide : 365297709 ≤ 365428781) S174C02.total S174C03.total

theorem join_0_2 : (twinPrimeSegment 365428781 365690925).card = 887 := by
  simpa using combineTwinPrimeSegments (by decide : 365428781 ≤ 365559853)
    (by decide : 365559853 ≤ 365690925) S174C04.total S174C05.total

theorem join_0_3 : (twinPrimeSegment 365690925 365953069).card = 846 := by
  simpa using combineTwinPrimeSegments (by decide : 365690925 ≤ 365821997)
    (by decide : 365821997 ≤ 365953069) S174C06.total S174C07.total

theorem join_0_4 : (twinPrimeSegment 365953069 366215213).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 365953069 ≤ 366084141)
    (by decide : 366084141 ≤ 366215213) S174C08.total S174C09.total

theorem join_0_5 : (twinPrimeSegment 366215213 366477357).card = 868 := by
  simpa using combineTwinPrimeSegments (by decide : 366215213 ≤ 366346285)
    (by decide : 366346285 ≤ 366477357) S174C10.total S174C11.total

theorem join_0_6 : (twinPrimeSegment 366477357 366739501).card = 905 := by
  simpa using combineTwinPrimeSegments (by decide : 366477357 ≤ 366608429)
    (by decide : 366608429 ≤ 366739501) S174C12.total S174C13.total

theorem join_0_7 : (twinPrimeSegment 366739501 367001645).card = 885 := by
  simpa using combineTwinPrimeSegments (by decide : 366739501 ≤ 366870573)
    (by decide : 366870573 ≤ 367001645) S174C14.total S174C15.total

theorem join_1_0 : (twinPrimeSegment 364904493 365428781).card = 1787 := by
  simpa using combineTwinPrimeSegments (by decide : 364904493 ≤ 365166637)
    (by decide : 365166637 ≤ 365428781) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 365428781 365953069).card = 1733 := by
  simpa using combineTwinPrimeSegments (by decide : 365428781 ≤ 365690925)
    (by decide : 365690925 ≤ 365953069) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 365953069 366477357).card = 1782 := by
  simpa using combineTwinPrimeSegments (by decide : 365953069 ≤ 366215213)
    (by decide : 366215213 ≤ 366477357) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 366477357 367001645).card = 1790 := by
  simpa using combineTwinPrimeSegments (by decide : 366477357 ≤ 366739501)
    (by decide : 366739501 ≤ 367001645) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 364904493 365953069).card = 3520 := by
  simpa using combineTwinPrimeSegments (by decide : 364904493 ≤ 365428781)
    (by decide : 365428781 ≤ 365953069) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 365953069 367001645).card = 3572 := by
  simpa using combineTwinPrimeSegments (by decide : 365953069 ≤ 366477357)
    (by decide : 366477357 ≤ 367001645) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 364904493 367001645).card = 7092 := by
  simpa using combineTwinPrimeSegments (by decide : 364904493 ≤ 365953069)
    (by decide : 365953069 ≤ 367001645) join_2_0 join_2_1

theorem total : (twinPrimeSegment 364904493 367001645).card = 7092 := join_3_0

end S174All
end Sude.GeneratedTwinScan
