import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19127)) 365821997 365854765 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365821997 365854765).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19127 365821997 365854765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19128)) 365854765 365887533 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365854765 365887533).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19128 365854765 365887533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19129)) 365887533 365920301 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 365887533 365920301).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19129 365887533 365920301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19129)) 365920301 365953069 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365920301 365953069).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19129 365920301 365953069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365821997 365887533).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 365821997 ≤ 365854765)
    (by decide : 365854765 ≤ 365887533) block0 block1

theorem join_0_1 : (twinPrimeSegment 365887533 365953069).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 365887533 ≤ 365920301)
    (by decide : 365920301 ≤ 365953069) block2 block3

theorem join_1_0 : (twinPrimeSegment 365821997 365953069).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 365821997 ≤ 365887533)
    (by decide : 365887533 ≤ 365953069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365821997 365953069).card = 417 := join_1_0

end S174C07
end Sude.GeneratedTwinScan
