import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17726)) 314179629 314212397 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 314179629 314212397).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17726 314179629 314212397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17726)) 314212397 314245165 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 314212397 314245165).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17726 314212397 314245165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17727)) 314245165 314277933 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 314245165 314277933).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17727 314245165 314277933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17728)) 314277933 314310701 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 314277933 314310701).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17728 314277933 314310701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 314179629 314245165).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 314179629 ≤ 314212397)
    (by decide : 314212397 ≤ 314245165) block0 block1

theorem join_0_1 : (twinPrimeSegment 314245165 314310701).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 314245165 ≤ 314277933)
    (by decide : 314277933 ≤ 314310701) block2 block3

theorem join_1_0 : (twinPrimeSegment 314179629 314310701).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 314179629 ≤ 314245165)
    (by decide : 314245165 ≤ 314310701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 314179629 314310701).card = 466 := join_1_0

end S149C13
end Sude.GeneratedTwinScan
