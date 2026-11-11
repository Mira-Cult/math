import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16768)) 281149485 281182253 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 281149485 281182253).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16768 281149485 281182253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16769)) 281182253 281215021 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 281182253 281215021).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16769 281182253 281215021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16770)) 281215021 281247789 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 281215021 281247789).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16770 281215021 281247789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16771)) 281247789 281280557 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 281247789 281280557).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16771 281247789 281280557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 281149485 281215021).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 281149485 ≤ 281182253)
    (by decide : 281182253 ≤ 281215021) block0 block1

theorem join_0_1 : (twinPrimeSegment 281215021 281280557).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 281215021 ≤ 281247789)
    (by decide : 281247789 ≤ 281280557) block2 block3

theorem join_1_0 : (twinPrimeSegment 281149485 281280557).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 281149485 ≤ 281215021)
    (by decide : 281215021 ≤ 281280557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 281149485 281280557).card = 489 := join_1_0

end S134C01
end Sude.GeneratedTwinScan
