import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15719)) 247070765 247103533 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 247070765 247103533).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15719 247070765 247103533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15720)) 247103533 247136301 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 247103533 247136301).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15720 247103533 247136301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15721)) 247136301 247169069 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 247136301 247169069).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15721 247136301 247169069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15722)) 247169069 247201837 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 247169069 247201837).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15722 247169069 247201837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 247070765 247136301).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 247070765 ≤ 247103533)
    (by decide : 247103533 ≤ 247136301) block0 block1

theorem join_0_1 : (twinPrimeSegment 247136301 247201837).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 247136301 ≤ 247169069)
    (by decide : 247169069 ≤ 247201837) block2 block3

theorem join_1_0 : (twinPrimeSegment 247070765 247201837).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 247070765 ≤ 247136301)
    (by decide : 247136301 ≤ 247201837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 247070765 247201837).card = 439 := join_1_0

end S117C13
end Sude.GeneratedTwinScan
