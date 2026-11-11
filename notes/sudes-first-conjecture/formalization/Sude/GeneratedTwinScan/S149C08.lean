import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17707)) 313524269 313557037 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 313524269 313557037).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17707 313524269 313557037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17708)) 313557037 313589805 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 313557037 313589805).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17708 313557037 313589805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17709)) 313589805 313622573 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 313589805 313622573).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17709 313589805 313622573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17710)) 313622573 313655341 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 313622573 313655341).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17710 313622573 313655341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 313524269 313589805).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 313524269 ≤ 313557037)
    (by decide : 313557037 ≤ 313589805) block0 block1

theorem join_0_1 : (twinPrimeSegment 313589805 313655341).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 313589805 ≤ 313622573)
    (by decide : 313622573 ≤ 313655341) block2 block3

theorem join_1_0 : (twinPrimeSegment 313524269 313655341).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 313524269 ≤ 313589805)
    (by decide : 313589805 ≤ 313655341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 313524269 313655341).card = 446 := join_1_0

end S149C08
end Sude.GeneratedTwinScan
