import Sude.GeneratedTwinScan.S198C00
import Sude.GeneratedTwinScan.S198C01
import Sude.GeneratedTwinScan.S198C02
import Sude.GeneratedTwinScan.S198C03
import Sude.GeneratedTwinScan.S198C04
import Sude.GeneratedTwinScan.S198C05
import Sude.GeneratedTwinScan.S198C06
import Sude.GeneratedTwinScan.S198C07
import Sude.GeneratedTwinScan.S198C08
import Sude.GeneratedTwinScan.S198C09
import Sude.GeneratedTwinScan.S198C10
import Sude.GeneratedTwinScan.S198C11
import Sude.GeneratedTwinScan.S198C12
import Sude.GeneratedTwinScan.S198C13
import Sude.GeneratedTwinScan.S198C14
import Sude.GeneratedTwinScan.S198C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S198All

theorem join_0_0 : (twinPrimeSegment 415236141 415498285).card = 874 := by
  simpa using combineTwinPrimeSegments (by decide : 415236141 ≤ 415367213)
    (by decide : 415367213 ≤ 415498285) S198C00.total S198C01.total

theorem join_0_1 : (twinPrimeSegment 415498285 415760429).card = 821 := by
  simpa using combineTwinPrimeSegments (by decide : 415498285 ≤ 415629357)
    (by decide : 415629357 ≤ 415760429) S198C02.total S198C03.total

theorem join_0_2 : (twinPrimeSegment 415760429 416022573).card = 870 := by
  simpa using combineTwinPrimeSegments (by decide : 415760429 ≤ 415891501)
    (by decide : 415891501 ≤ 416022573) S198C04.total S198C05.total

theorem join_0_3 : (twinPrimeSegment 416022573 416284717).card = 865 := by
  simpa using combineTwinPrimeSegments (by decide : 416022573 ≤ 416153645)
    (by decide : 416153645 ≤ 416284717) S198C06.total S198C07.total

theorem join_0_4 : (twinPrimeSegment 416284717 416546861).card = 891 := by
  simpa using combineTwinPrimeSegments (by decide : 416284717 ≤ 416415789)
    (by decide : 416415789 ≤ 416546861) S198C08.total S198C09.total

theorem join_0_5 : (twinPrimeSegment 416546861 416809005).card = 917 := by
  simpa using combineTwinPrimeSegments (by decide : 416546861 ≤ 416677933)
    (by decide : 416677933 ≤ 416809005) S198C10.total S198C11.total

theorem join_0_6 : (twinPrimeSegment 416809005 417071149).card = 903 := by
  simpa using combineTwinPrimeSegments (by decide : 416809005 ≤ 416940077)
    (by decide : 416940077 ≤ 417071149) S198C12.total S198C13.total

theorem join_0_7 : (twinPrimeSegment 417071149 417333293).card = 910 := by
  simpa using combineTwinPrimeSegments (by decide : 417071149 ≤ 417202221)
    (by decide : 417202221 ≤ 417333293) S198C14.total S198C15.total

theorem join_1_0 : (twinPrimeSegment 415236141 415760429).card = 1695 := by
  simpa using combineTwinPrimeSegments (by decide : 415236141 ≤ 415498285)
    (by decide : 415498285 ≤ 415760429) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 415760429 416284717).card = 1735 := by
  simpa using combineTwinPrimeSegments (by decide : 415760429 ≤ 416022573)
    (by decide : 416022573 ≤ 416284717) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 416284717 416809005).card = 1808 := by
  simpa using combineTwinPrimeSegments (by decide : 416284717 ≤ 416546861)
    (by decide : 416546861 ≤ 416809005) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 416809005 417333293).card = 1813 := by
  simpa using combineTwinPrimeSegments (by decide : 416809005 ≤ 417071149)
    (by decide : 417071149 ≤ 417333293) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 415236141 416284717).card = 3430 := by
  simpa using combineTwinPrimeSegments (by decide : 415236141 ≤ 415760429)
    (by decide : 415760429 ≤ 416284717) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 416284717 417333293).card = 3621 := by
  simpa using combineTwinPrimeSegments (by decide : 416284717 ≤ 416809005)
    (by decide : 416809005 ≤ 417333293) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 415236141 417333293).card = 7051 := by
  simpa using combineTwinPrimeSegments (by decide : 415236141 ≤ 416284717)
    (by decide : 416284717 ≤ 417333293) join_2_0 join_2_1

theorem total : (twinPrimeSegment 415236141 417333293).card = 7051 := join_3_0

end S198All
end Sude.GeneratedTwinScan
