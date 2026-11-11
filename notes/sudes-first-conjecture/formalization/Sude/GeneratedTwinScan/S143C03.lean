import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17329)) 300285997 300318765 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300285997 300318765).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17329 300285997 300318765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17330)) 300318765 300351533 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300318765 300351533).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17330 300318765 300351533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17331)) 300351533 300384301 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 300351533 300384301).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17331 300351533 300384301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17332)) 300384301 300417069 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 300384301 300417069).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17332 300384301 300417069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300285997 300351533).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 300285997 ≤ 300318765)
    (by decide : 300318765 ≤ 300351533) block0 block1

theorem join_0_1 : (twinPrimeSegment 300351533 300417069).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 300351533 ≤ 300384301)
    (by decide : 300384301 ≤ 300417069) block2 block3

theorem join_1_0 : (twinPrimeSegment 300285997 300417069).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 300285997 ≤ 300351533)
    (by decide : 300351533 ≤ 300417069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300285997 300417069).card = 474 := join_1_0

end S143C03
end Sude.GeneratedTwinScan
