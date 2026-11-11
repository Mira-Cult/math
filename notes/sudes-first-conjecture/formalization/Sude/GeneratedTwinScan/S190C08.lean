import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19988)) 399507501 399540269 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 399507501 399540269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19988 399507501 399540269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19989)) 399540269 399573037 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 399540269 399573037).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19989 399540269 399573037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19990)) 399573037 399605805 = 90 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 399573037 399605805).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19990 399573037 399605805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19990)) 399605805 399638573 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 399605805 399638573).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19990 399605805 399638573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 399507501 399573037).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 399507501 ≤ 399540269)
    (by decide : 399540269 ≤ 399573037) block0 block1

theorem join_0_1 : (twinPrimeSegment 399573037 399638573).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 399573037 ≤ 399605805)
    (by decide : 399605805 ≤ 399638573) block2 block3

theorem join_1_0 : (twinPrimeSegment 399507501 399638573).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 399507501 ≤ 399573037)
    (by decide : 399573037 ≤ 399638573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 399507501 399638573).card = 413 := join_1_0

end S190C08
end Sude.GeneratedTwinScan
