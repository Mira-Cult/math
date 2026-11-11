import Sude.GeneratedTwinScan.S173C00
import Sude.GeneratedTwinScan.S173C01
import Sude.GeneratedTwinScan.S173C02
import Sude.GeneratedTwinScan.S173C03
import Sude.GeneratedTwinScan.S173C04
import Sude.GeneratedTwinScan.S173C05
import Sude.GeneratedTwinScan.S173C06
import Sude.GeneratedTwinScan.S173C07
import Sude.GeneratedTwinScan.S173C08
import Sude.GeneratedTwinScan.S173C09
import Sude.GeneratedTwinScan.S173C10
import Sude.GeneratedTwinScan.S173C11
import Sude.GeneratedTwinScan.S173C12
import Sude.GeneratedTwinScan.S173C13
import Sude.GeneratedTwinScan.S173C14
import Sude.GeneratedTwinScan.S173C15

/-! Combined FT source segment; Lean kernel check required. -/
namespace Sude.GeneratedTwinScan
namespace S173All

theorem join_0_0 : (twinPrimeSegment 362807341 363069485).card = 960 := by
  simpa using combineTwinPrimeSegments (by decide : 362807341 ≤ 362938413)
    (by decide : 362938413 ≤ 363069485) S173C00.total S173C01.total

theorem join_0_1 : (twinPrimeSegment 363069485 363331629).card = 898 := by
  simpa using combineTwinPrimeSegments (by decide : 363069485 ≤ 363200557)
    (by decide : 363200557 ≤ 363331629) S173C02.total S173C03.total

theorem join_0_2 : (twinPrimeSegment 363331629 363593773).card = 923 := by
  simpa using combineTwinPrimeSegments (by decide : 363331629 ≤ 363462701)
    (by decide : 363462701 ≤ 363593773) S173C04.total S173C05.total

theorem join_0_3 : (twinPrimeSegment 363593773 363855917).card = 922 := by
  simpa using combineTwinPrimeSegments (by decide : 363593773 ≤ 363724845)
    (by decide : 363724845 ≤ 363855917) S173C06.total S173C07.total

theorem join_0_4 : (twinPrimeSegment 363855917 364118061).card = 881 := by
  simpa using combineTwinPrimeSegments (by decide : 363855917 ≤ 363986989)
    (by decide : 363986989 ≤ 364118061) S173C08.total S173C09.total

theorem join_0_5 : (twinPrimeSegment 364118061 364380205).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 364118061 ≤ 364249133)
    (by decide : 364249133 ≤ 364380205) S173C10.total S173C11.total

theorem join_0_6 : (twinPrimeSegment 364380205 364642349).card = 864 := by
  simpa using combineTwinPrimeSegments (by decide : 364380205 ≤ 364511277)
    (by decide : 364511277 ≤ 364642349) S173C12.total S173C13.total

theorem join_0_7 : (twinPrimeSegment 364642349 364904493).card = 896 := by
  simpa using combineTwinPrimeSegments (by decide : 364642349 ≤ 364773421)
    (by decide : 364773421 ≤ 364904493) S173C14.total S173C15.total

theorem join_1_0 : (twinPrimeSegment 362807341 363331629).card = 1858 := by
  simpa using combineTwinPrimeSegments (by decide : 362807341 ≤ 363069485)
    (by decide : 363069485 ≤ 363331629) join_0_0 join_0_1

theorem join_1_1 : (twinPrimeSegment 363331629 363855917).card = 1845 := by
  simpa using combineTwinPrimeSegments (by decide : 363331629 ≤ 363593773)
    (by decide : 363593773 ≤ 363855917) join_0_2 join_0_3

theorem join_1_2 : (twinPrimeSegment 363855917 364380205).card = 1794 := by
  simpa using combineTwinPrimeSegments (by decide : 363855917 ≤ 364118061)
    (by decide : 364118061 ≤ 364380205) join_0_4 join_0_5

theorem join_1_3 : (twinPrimeSegment 364380205 364904493).card = 1760 := by
  simpa using combineTwinPrimeSegments (by decide : 364380205 ≤ 364642349)
    (by decide : 364642349 ≤ 364904493) join_0_6 join_0_7

theorem join_2_0 : (twinPrimeSegment 362807341 363855917).card = 3703 := by
  simpa using combineTwinPrimeSegments (by decide : 362807341 ≤ 363331629)
    (by decide : 363331629 ≤ 363855917) join_1_0 join_1_1

theorem join_2_1 : (twinPrimeSegment 363855917 364904493).card = 3554 := by
  simpa using combineTwinPrimeSegments (by decide : 363855917 ≤ 364380205)
    (by decide : 364380205 ≤ 364904493) join_1_2 join_1_3

theorem join_3_0 : (twinPrimeSegment 362807341 364904493).card = 7257 := by
  simpa using combineTwinPrimeSegments (by decide : 362807341 ≤ 363855917)
    (by decide : 363855917 ≤ 364904493) join_2_0 join_2_1

theorem total : (twinPrimeSegment 362807341 364904493).card = 7257 := join_3_0

end S173All
end Sude.GeneratedTwinScan
