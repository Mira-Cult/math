import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20271)) 410910765 410943533 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 410910765 410943533).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20271 410910765 410943533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20272)) 410943533 410976301 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 410943533 410976301).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20272 410943533 410976301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20273)) 410976301 411009069 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 410976301 411009069).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20273 410976301 411009069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20274)) 411009069 411041837 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 411009069 411041837).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20274 411009069 411041837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 410910765 410976301).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 410910765 ≤ 410943533)
    (by decide : 410943533 ≤ 410976301) block0 block1

theorem join_0_1 : (twinPrimeSegment 410976301 411041837).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 410976301 ≤ 411009069)
    (by decide : 411009069 ≤ 411041837) block2 block3

theorem join_1_0 : (twinPrimeSegment 410910765 411041837).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 410910765 ≤ 410976301)
    (by decide : 410976301 ≤ 411041837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 410910765 411041837).card = 457 := join_1_0

end S195C15
end Sude.GeneratedTwinScan
