import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13957)) 194773037 194805805 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 194773037 194805805).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13957 194773037 194805805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13958)) 194805805 194838573 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 194805805 194838573).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13958 194805805 194838573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13959)) 194838573 194871341 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 194838573 194871341).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13959 194838573 194871341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13960)) 194871341 194904109 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 194871341 194904109).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13960 194871341 194904109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 194773037 194838573).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 194773037 ≤ 194805805)
    (by decide : 194805805 ≤ 194838573) block0 block1

theorem join_0_1 : (twinPrimeSegment 194838573 194904109).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 194838573 ≤ 194871341)
    (by decide : 194871341 ≤ 194904109) block2 block3

theorem join_1_0 : (twinPrimeSegment 194773037 194904109).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 194773037 ≤ 194838573)
    (by decide : 194838573 ≤ 194904109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 194773037 194904109).card = 501 := join_1_0

end S092C14
end Sude.GeneratedTwinScan
