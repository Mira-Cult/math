import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16741)) 280231981 280264749 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 280231981 280264749).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16741 280231981 280264749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16742)) 280264749 280297517 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280264749 280297517).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16742 280264749 280297517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16743)) 280297517 280330285 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280297517 280330285).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16743 280297517 280330285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16744)) 280330285 280363053 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280330285 280363053).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16744 280330285 280363053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 280231981 280297517).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 280231981 ≤ 280264749)
    (by decide : 280264749 ≤ 280297517) block0 block1

theorem join_0_1 : (twinPrimeSegment 280297517 280363053).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 280297517 ≤ 280330285)
    (by decide : 280330285 ≤ 280363053) block2 block3

theorem join_1_0 : (twinPrimeSegment 280231981 280363053).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 280231981 ≤ 280297517)
    (by decide : 280297517 ≤ 280363053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 280231981 280363053).card = 476 := join_1_0

end S133C10
end Sude.GeneratedTwinScan
