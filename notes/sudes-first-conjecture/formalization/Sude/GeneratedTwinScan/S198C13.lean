import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20419)) 416940077 416972845 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416940077 416972845).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20419 416940077 416972845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20420)) 416972845 417005613 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416972845 417005613).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20420 416972845 417005613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20421)) 417005613 417038381 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417005613 417038381).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20421 417005613 417038381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20422)) 417038381 417071149 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417038381 417071149).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20422 417038381 417071149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416940077 417005613).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 416940077 ≤ 416972845)
    (by decide : 416972845 ≤ 417005613) block0 block1

theorem join_0_1 : (twinPrimeSegment 417005613 417071149).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 417005613 ≤ 417038381)
    (by decide : 417038381 ≤ 417071149) block2 block3

theorem join_1_0 : (twinPrimeSegment 416940077 417071149).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 416940077 ≤ 417005613)
    (by decide : 417005613 ≤ 417071149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416940077 417071149).card = 438 := join_1_0

end S198C13
end Sude.GeneratedTwinScan
