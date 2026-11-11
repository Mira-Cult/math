import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134479917 134512685 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 134479917 134512685).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134479917 134512685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134512685 134545453 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 134512685 134545453).card = 96 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134512685 134545453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134545453 134578221 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134545453 134578221).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134545453 134578221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134578221 134610989 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134578221 134610989).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134578221 134610989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 134479917 134545453).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 134479917 ≤ 134512685)
    (by decide : 134512685 ≤ 134545453) block0 block1

theorem join_0_1 : (twinPrimeSegment 134545453 134610989).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 134545453 ≤ 134578221)
    (by decide : 134578221 ≤ 134610989) block2 block3

theorem join_1_0 : (twinPrimeSegment 134479917 134610989).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 134479917 ≤ 134545453)
    (by decide : 134545453 ≤ 134610989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 134479917 134610989).card = 439 := join_1_0

end S064C02
end Sude.GeneratedTwinScan
