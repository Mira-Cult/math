import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22875)) 523239469 523272237 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 523239469 523272237).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22875 523239469 523272237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22875)) 523272237 523305005 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523272237 523305005).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22875 523272237 523305005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22876)) 523305005 523337773 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523305005 523337773).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22876 523305005 523337773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22877)) 523337773 523370541 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523337773 523370541).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22877 523337773 523370541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 523239469 523305005).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 523239469 ≤ 523272237)
    (by decide : 523272237 ≤ 523305005) block0 block1

theorem join_0_1 : (twinPrimeSegment 523305005 523370541).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 523305005 ≤ 523337773)
    (by decide : 523337773 ≤ 523370541) block2 block3

theorem join_1_0 : (twinPrimeSegment 523239469 523370541).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 523239469 ≤ 523305005)
    (by decide : 523305005 ≤ 523370541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 523239469 523370541).card = 489 := join_1_0

end S249C08
end Sude.GeneratedTwinScan
