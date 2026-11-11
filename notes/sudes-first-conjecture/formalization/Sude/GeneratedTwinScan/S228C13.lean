import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21906)) 479854637 479887405 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 479854637 479887405).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21906 479854637 479887405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21907)) 479887405 479920173 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 479887405 479920173).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21907 479887405 479920173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21907)) 479920173 479952941 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 479920173 479952941).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21907 479920173 479952941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21908)) 479952941 479985709 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 479952941 479985709).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21908 479952941 479985709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 479854637 479920173).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 479854637 ≤ 479887405)
    (by decide : 479887405 ≤ 479920173) block0 block1

theorem join_0_1 : (twinPrimeSegment 479920173 479985709).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 479920173 ≤ 479952941)
    (by decide : 479952941 ≤ 479985709) block2 block3

theorem join_1_0 : (twinPrimeSegment 479854637 479985709).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 479854637 ≤ 479920173)
    (by decide : 479920173 ≤ 479985709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 479854637 479985709).card = 422 := join_1_0

end S228C13
end Sude.GeneratedTwinScan
