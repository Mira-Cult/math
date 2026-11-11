import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19446)) 378142765 378175533 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 378142765 378175533).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19446 378142765 378175533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19447)) 378175533 378208301 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 378175533 378208301).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19447 378175533 378208301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19448)) 378208301 378241069 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 378208301 378241069).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19448 378208301 378241069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19449)) 378241069 378273837 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 378241069 378273837).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19449 378241069 378273837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 378142765 378208301).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 378142765 ≤ 378175533)
    (by decide : 378175533 ≤ 378208301) block0 block1

theorem join_0_1 : (twinPrimeSegment 378208301 378273837).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 378208301 ≤ 378241069)
    (by decide : 378241069 ≤ 378273837) block2 block3

theorem join_1_0 : (twinPrimeSegment 378142765 378273837).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 378142765 ≤ 378208301)
    (by decide : 378208301 ≤ 378273837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 378142765 378273837).card = 434 := join_1_0

end S180C05
end Sude.GeneratedTwinScan
