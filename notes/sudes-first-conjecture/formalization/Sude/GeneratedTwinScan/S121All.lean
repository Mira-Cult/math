import Sude.GeneratedTwinScan.S121C00
import Sude.GeneratedTwinScan.S121C01
import Sude.GeneratedTwinScan.S121C02
import Sude.GeneratedTwinScan.S121C03
import Sude.GeneratedTwinScan.S121C04
import Sude.GeneratedTwinScan.S121C05
import Sude.GeneratedTwinScan.S121C06
import Sude.GeneratedTwinScan.S121C07
import Sude.GeneratedTwinScan.S121C08
import Sude.GeneratedTwinScan.S121C09
import Sude.GeneratedTwinScan.S121C10
import Sude.GeneratedTwinScan.S121C11
import Sude.GeneratedTwinScan.S121C12
import Sude.GeneratedTwinScan.S121C13
import Sude.GeneratedTwinScan.S121C14
import Sude.GeneratedTwinScan.S121C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S121All

theorem join_0_0 : (twinPrimeSegment 253755437 254017581).card = 944 := by
  simpa using combineTwinPrimeSegments (by decide : 253755437 ≤ 253886509)
    (by decide : 253886509 ≤ 254017581) S121C00.total S121C01.total

theorem join_0_1 : (twinPrimeSegment 254017581 254279725).card = 908 := by
  simpa using combineTwinPrimeSegments (by decide : 254017581 ≤ 254148653)
    (by decide : 254148653 ≤ 254279725) S121C02.total S121C03.total

theorem join_0_2 : (twinPrimeSegment 254279725 254541869).card = 957 := by
  simpa using combineTwinPrimeSegments (by decide : 254279725 ≤ 254410797)
    (by decide : 254410797 ≤ 254541869) S121C04.total S121C05.total

theorem join_0_3 : (twinPrimeSegment 254541869 254804013).card = 950 := by
  simpa using combineTwinPrimeSegments (by decide : 254541869 ≤ 254672941)
    (by decide : 254672941 ≤ 254804013) S121C06.total S121C07.total

theorem join_0_4 : (twinPrimeSegment 254804013 255066157).card = 984 := by
  simpa using combineTwinPrimeSegments (by decide : 254804013 ≤ 254935085)
    (by decide : 254935085 ≤ 255066157) S121C08.total S121C09.total

theorem join_0_5 : (twinPrimeSegment 255066157 255328301).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 255066157 ≤ 255197229)
    (by decide : 255197229 ≤ 255328301) S121C10.total S121C11.total

theorem join_0_6 : (twinPrimeSegment 255328301 255590445).card = 915 := by
  simpa using combineTwinPrimeSegments (by decide : 255328301 ≤ 255459373)
    (by decide : 255459373 ≤ 255590445) S121C12.total S121C13.total

theorem join_0_7 : (twinPrimeSegment 255590445 255852589).card = 930 := by
  simpa using combineTwinPrimeSegments (by decide : 255590445 ≤ 255721517)
    (by decide : 255721517 ≤ 255852589) S121C14.total S121C15.total

theorem join_1_0 : (twinPrimeSegment 253755437 254279725).card = 1852 := by
  simpa using combineTwinPrimeSegments (by decide : 253755437 ≤ 254017581)
    (by decide : 254017581 ≤ 254279725) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 254279725 254804013).card = 1907 := by
  simpa using combineTwinPrimeSegments (by decide : 254279725 ≤ 254541869)
    (by decide : 254541869 ≤ 254804013) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 254804013 255328301).card = 1894 := by
  simpa using combineTwinPrimeSegments (by decide : 254804013 ≤ 255066157)
    (by decide : 255066157 ≤ 255328301) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 255328301 255852589).card = 1845 := by
  simpa using combineTwinPrimeSegments (by decide : 255328301 ≤ 255590445)
    (by decide : 255590445 ≤ 255852589) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 253755437 254804013).card = 3759 := by
  simpa using combineTwinPrimeSegments (by decide : 253755437 ≤ 254279725)
    (by decide : 254279725 ≤ 254804013) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 254804013 255852589).card = 3739 := by
  simpa using combineTwinPrimeSegments (by decide : 254804013 ≤ 255328301)
    (by decide : 255328301 ≤ 255852589) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 253755437 255852589).card = 7498 := by
  simpa using combineTwinPrimeSegments (by decide : 253755437 ≤ 254804013)
    (by decide : 254804013 ≤ 255852589) join_2_0 join_2_1

theorem total : (twinPrimeSegment 253755437 255852589).card = 7498 := join_3_0

end S121All
end Sude.GeneratedTwinScan
