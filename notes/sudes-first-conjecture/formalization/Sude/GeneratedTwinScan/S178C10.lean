import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19355)) 374603821 374636589 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 374603821 374636589).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19355 374603821 374636589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19356)) 374636589 374669357 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 374636589 374669357).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19356 374636589 374669357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19357)) 374669357 374702125 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 374669357 374702125).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19357 374669357 374702125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19358)) 374702125 374734893 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 374702125 374734893).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19358 374702125 374734893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 374603821 374669357).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 374603821 ≤ 374636589)
    (by decide : 374636589 ≤ 374669357) block0 block1

theorem join_0_1 : (twinPrimeSegment 374669357 374734893).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 374669357 ≤ 374702125)
    (by decide : 374702125 ≤ 374734893) block2 block3

theorem join_1_0 : (twinPrimeSegment 374603821 374734893).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 374603821 ≤ 374669357)
    (by decide : 374669357 ≤ 374734893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 374603821 374734893).card = 416 := join_1_0

end S178C10
end Sude.GeneratedTwinScan
