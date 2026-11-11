import Sude.GeneratedTwinScan.S082C00
import Sude.GeneratedTwinScan.S082C01
import Sude.GeneratedTwinScan.S082C02
import Sude.GeneratedTwinScan.S082C03
import Sude.GeneratedTwinScan.S082C04
import Sude.GeneratedTwinScan.S082C05
import Sude.GeneratedTwinScan.S082C06
import Sude.GeneratedTwinScan.S082C07
import Sude.GeneratedTwinScan.S082C08
import Sude.GeneratedTwinScan.S082C09
import Sude.GeneratedTwinScan.S082C10
import Sude.GeneratedTwinScan.S082C11
import Sude.GeneratedTwinScan.S082C12
import Sude.GeneratedTwinScan.S082C13
import Sude.GeneratedTwinScan.S082C14
import Sude.GeneratedTwinScan.S082C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S082All

theorem join_0_0 : (twinPrimeSegment 171966509 172228653).card = 914 := by
  simpa using combineTwinPrimeSegments (by decide : 171966509 ≤ 172097581)
    (by decide : 172097581 ≤ 172228653) S082C00.total S082C01.total

theorem join_0_1 : (twinPrimeSegment 172228653 172490797).card = 981 := by
  simpa using combineTwinPrimeSegments (by decide : 172228653 ≤ 172359725)
    (by decide : 172359725 ≤ 172490797) S082C02.total S082C03.total

theorem join_0_2 : (twinPrimeSegment 172490797 172752941).card = 952 := by
  simpa using combineTwinPrimeSegments (by decide : 172490797 ≤ 172621869)
    (by decide : 172621869 ≤ 172752941) S082C04.total S082C05.total

theorem join_0_3 : (twinPrimeSegment 172752941 173015085).card = 924 := by
  simpa using combineTwinPrimeSegments (by decide : 172752941 ≤ 172884013)
    (by decide : 172884013 ≤ 173015085) S082C06.total S082C07.total

theorem join_0_4 : (twinPrimeSegment 173015085 173277229).card = 981 := by
  simpa using combineTwinPrimeSegments (by decide : 173015085 ≤ 173146157)
    (by decide : 173146157 ≤ 173277229) S082C08.total S082C09.total

theorem join_0_5 : (twinPrimeSegment 173277229 173539373).card = 975 := by
  simpa using combineTwinPrimeSegments (by decide : 173277229 ≤ 173408301)
    (by decide : 173408301 ≤ 173539373) S082C10.total S082C11.total

theorem join_0_6 : (twinPrimeSegment 173539373 173801517).card = 952 := by
  simpa using combineTwinPrimeSegments (by decide : 173539373 ≤ 173670445)
    (by decide : 173670445 ≤ 173801517) S082C12.total S082C13.total

theorem join_0_7 : (twinPrimeSegment 173801517 174063661).card = 943 := by
  simpa using combineTwinPrimeSegments (by decide : 173801517 ≤ 173932589)
    (by decide : 173932589 ≤ 174063661) S082C14.total S082C15.total

theorem join_1_0 : (twinPrimeSegment 171966509 172490797).card = 1895 := by
  simpa using combineTwinPrimeSegments (by decide : 171966509 ≤ 172228653)
    (by decide : 172228653 ≤ 172490797) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 172490797 173015085).card = 1876 := by
  simpa using combineTwinPrimeSegments (by decide : 172490797 ≤ 172752941)
    (by decide : 172752941 ≤ 173015085) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 173015085 173539373).card = 1956 := by
  simpa using combineTwinPrimeSegments (by decide : 173015085 ≤ 173277229)
    (by decide : 173277229 ≤ 173539373) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 173539373 174063661).card = 1895 := by
  simpa using combineTwinPrimeSegments (by decide : 173539373 ≤ 173801517)
    (by decide : 173801517 ≤ 174063661) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 171966509 173015085).card = 3771 := by
  simpa using combineTwinPrimeSegments (by decide : 171966509 ≤ 172490797)
    (by decide : 172490797 ≤ 173015085) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 173015085 174063661).card = 3851 := by
  simpa using combineTwinPrimeSegments (by decide : 173015085 ≤ 173539373)
    (by decide : 173539373 ≤ 174063661) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 171966509 174063661).card = 7622 := by
  simpa using combineTwinPrimeSegments (by decide : 171966509 ≤ 173015085)
    (by decide : 173015085 ≤ 174063661) join_2_0 join_2_1

theorem total : (twinPrimeSegment 171966509 174063661).card = 7622 := join_3_0

end S082All
end Sude.GeneratedTwinScan
