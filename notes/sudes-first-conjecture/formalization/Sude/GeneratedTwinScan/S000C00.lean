import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.FiniteTwinLowActive65536

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem block0 : (twinPrimeSegment 45 32813).card = 500 :=
  finiteTwinLowBlock0_mathematical

theorem block1 : (twinPrimeSegment 32813 65581).card = 356 :=
  finiteTwinLowBlock1_mathematical

theorem block2 : (twinPrimeSegment 65581 98349).card = 344 :=
  finiteTwinLowBlock2_mathematical

theorem block3 : (twinPrimeSegment 98349 131117).card = 321 :=
  finiteTwinLowBlock3_mathematical

theorem join_0_0 : (twinPrimeSegment 45 65581).card = 856 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 32813)
    (by decide : 32813 ≤ 65581) block0 block1

theorem join_0_1 : (twinPrimeSegment 65581 131117).card = 665 := by
  simpa using combineTwinPrimeSegments (by decide : 65581 ≤ 98349)
    (by decide : 98349 ≤ 131117) block2 block3

theorem join_1_0 : (twinPrimeSegment 45 131117).card = 1521 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 65581)
    (by decide : 65581 ≤ 131117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 45 131117).card = 1521 := join_1_0

end S000C00
end Sude.GeneratedTwinScan
