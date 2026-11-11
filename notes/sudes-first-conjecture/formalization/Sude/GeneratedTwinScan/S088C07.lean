import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13619)) 185466925 185499693 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185466925 185499693).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13619 185466925 185499693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13621)) 185499693 185532461 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 185499693 185532461).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13621 185499693 185532461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13622)) 185532461 185565229 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185532461 185565229).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13622 185532461 185565229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13623)) 185565229 185597997 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185565229 185597997).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13623 185565229 185597997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185466925 185532461).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 185466925 ≤ 185499693)
    (by decide : 185499693 ≤ 185532461) block0 block1

theorem join_0_1 : (twinPrimeSegment 185532461 185597997).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 185532461 ≤ 185565229)
    (by decide : 185565229 ≤ 185597997) block2 block3

theorem join_1_0 : (twinPrimeSegment 185466925 185597997).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 185466925 ≤ 185532461)
    (by decide : 185532461 ≤ 185597997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185466925 185597997).card = 456 := join_1_0

end S088C07
end Sude.GeneratedTwinScan
