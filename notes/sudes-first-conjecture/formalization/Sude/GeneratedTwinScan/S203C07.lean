import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20656)) 426639405 426672173 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 426639405 426672173).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20656 426639405 426672173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20656)) 426672173 426704941 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 426672173 426704941).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20656 426672173 426704941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20657)) 426704941 426737709 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 426704941 426737709).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20657 426704941 426737709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20658)) 426737709 426770477 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 426737709 426770477).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20658 426737709 426770477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 426639405 426704941).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 426639405 ≤ 426672173)
    (by decide : 426672173 ≤ 426704941) block0 block1

theorem join_0_1 : (twinPrimeSegment 426704941 426770477).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 426704941 ≤ 426737709)
    (by decide : 426737709 ≤ 426770477) block2 block3

theorem join_1_0 : (twinPrimeSegment 426639405 426770477).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 426639405 ≤ 426704941)
    (by decide : 426704941 ≤ 426770477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 426639405 426770477).card = 451 := join_1_0

end S203C07
end Sude.GeneratedTwinScan
