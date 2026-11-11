import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17356)) 301203501 301236269 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 301203501 301236269).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17356 301203501 301236269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17357)) 301236269 301269037 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 301236269 301269037).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17357 301236269 301269037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17358)) 301269037 301301805 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 301269037 301301805).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17358 301269037 301301805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17358)) 301301805 301334573 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 301301805 301334573).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17358 301301805 301334573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 301203501 301269037).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 301203501 ≤ 301236269)
    (by decide : 301236269 ≤ 301269037) block0 block1

theorem join_0_1 : (twinPrimeSegment 301269037 301334573).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 301269037 ≤ 301301805)
    (by decide : 301301805 ≤ 301334573) block2 block3

theorem join_1_0 : (twinPrimeSegment 301203501 301334573).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 301203501 ≤ 301269037)
    (by decide : 301269037 ≤ 301334573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 301203501 301334573).card = 448 := join_1_0

end S143C10
end Sude.GeneratedTwinScan
