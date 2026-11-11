import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12903)) 166461485 166494253 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166461485 166494253).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12903 166461485 166494253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12904)) 166494253 166527021 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 166494253 166527021).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12904 166494253 166527021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12905)) 166527021 166559789 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166527021 166559789).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12905 166527021 166559789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12907)) 166559789 166592557 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166559789 166592557).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12907 166559789 166592557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166461485 166527021).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 166461485 ≤ 166494253)
    (by decide : 166494253 ≤ 166527021) block0 block1

theorem join_0_1 : (twinPrimeSegment 166527021 166592557).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 166527021 ≤ 166559789)
    (by decide : 166559789 ≤ 166592557) block2 block3

theorem join_1_0 : (twinPrimeSegment 166461485 166592557).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 166461485 ≤ 166527021)
    (by decide : 166527021 ≤ 166592557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166461485 166592557).card = 472 := join_1_0

end S079C06
end Sude.GeneratedTwinScan
