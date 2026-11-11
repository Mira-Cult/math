import Sude.GeneratedTwinScan.S157C00
import Sude.GeneratedTwinScan.S157C01
import Sude.GeneratedTwinScan.S157C02
import Sude.GeneratedTwinScan.S157C03
import Sude.GeneratedTwinScan.S157C04
import Sude.GeneratedTwinScan.S157C05
import Sude.GeneratedTwinScan.S157C06
import Sude.GeneratedTwinScan.S157C07
import Sude.GeneratedTwinScan.S157C08
import Sude.GeneratedTwinScan.S157C09
import Sude.GeneratedTwinScan.S157C10
import Sude.GeneratedTwinScan.S157C11
import Sude.GeneratedTwinScan.S157C12
import Sude.GeneratedTwinScan.S157C13
import Sude.GeneratedTwinScan.S157C14
import Sude.GeneratedTwinScan.S157C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S157All

theorem join_0_0 : (twinPrimeSegment 329252909 329515053).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 329252909 ≤ 329383981)
    (by decide : 329383981 ≤ 329515053) S157C00.total S157C01.total

theorem join_0_1 : (twinPrimeSegment 329515053 329777197).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 329515053 ≤ 329646125)
    (by decide : 329646125 ≤ 329777197) S157C02.total S157C03.total

theorem join_0_2 : (twinPrimeSegment 329777197 330039341).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 329777197 ≤ 329908269)
    (by decide : 329908269 ≤ 330039341) S157C04.total S157C05.total

theorem join_0_3 : (twinPrimeSegment 330039341 330301485).card = 867 := by
  simpa using combineTwinPrimeSegments (by decide : 330039341 ≤ 330170413)
    (by decide : 330170413 ≤ 330301485) S157C06.total S157C07.total

theorem join_0_4 : (twinPrimeSegment 330301485 330563629).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 330301485 ≤ 330432557)
    (by decide : 330432557 ≤ 330563629) S157C08.total S157C09.total

theorem join_0_5 : (twinPrimeSegment 330563629 330825773).card = 893 := by
  simpa using combineTwinPrimeSegments (by decide : 330563629 ≤ 330694701)
    (by decide : 330694701 ≤ 330825773) S157C10.total S157C11.total

theorem join_0_6 : (twinPrimeSegment 330825773 331087917).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 330825773 ≤ 330956845)
    (by decide : 330956845 ≤ 331087917) S157C12.total S157C13.total

theorem join_0_7 : (twinPrimeSegment 331087917 331350061).card = 916 := by
  simpa using combineTwinPrimeSegments (by decide : 331087917 ≤ 331218989)
    (by decide : 331218989 ≤ 331350061) S157C14.total S157C15.total

theorem join_1_0 : (twinPrimeSegment 329252909 329777197).card = 1830 := by
  simpa using combineTwinPrimeSegments (by decide : 329252909 ≤ 329515053)
    (by decide : 329515053 ≤ 329777197) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 329777197 330301485).card = 1732 := by
  simpa using combineTwinPrimeSegments (by decide : 329777197 ≤ 330039341)
    (by decide : 330039341 ≤ 330301485) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 330301485 330825773).card = 1822 := by
  simpa using combineTwinPrimeSegments (by decide : 330301485 ≤ 330563629)
    (by decide : 330563629 ≤ 330825773) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 330825773 331350061).card = 1780 := by
  simpa using combineTwinPrimeSegments (by decide : 330825773 ≤ 331087917)
    (by decide : 331087917 ≤ 331350061) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 329252909 330301485).card = 3562 := by
  simpa using combineTwinPrimeSegments (by decide : 329252909 ≤ 329777197)
    (by decide : 329777197 ≤ 330301485) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 330301485 331350061).card = 3602 := by
  simpa using combineTwinPrimeSegments (by decide : 330301485 ≤ 330825773)
    (by decide : 330825773 ≤ 331350061) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 329252909 331350061).card = 7164 := by
  simpa using combineTwinPrimeSegments (by decide : 329252909 ≤ 330301485)
    (by decide : 330301485 ≤ 331350061) join_2_0 join_2_1

theorem total : (twinPrimeSegment 329252909 331350061).card = 7164 := join_3_0

end S157All
end Sude.GeneratedTwinScan
