import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20608)) 424673325 424706093 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 424673325 424706093).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20608 424673325 424706093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20609)) 424706093 424738861 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 424706093 424738861).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20609 424706093 424738861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20609)) 424738861 424771629 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 424738861 424771629).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20609 424738861 424771629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20610)) 424771629 424804397 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 424771629 424804397).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20610 424771629 424804397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 424673325 424738861).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 424673325 ≤ 424706093)
    (by decide : 424706093 ≤ 424738861) block0 block1

theorem join_0_1 : (twinPrimeSegment 424738861 424804397).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 424738861 ≤ 424771629)
    (by decide : 424771629 ≤ 424804397) block2 block3

theorem join_1_0 : (twinPrimeSegment 424673325 424804397).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 424673325 ≤ 424738861)
    (by decide : 424738861 ≤ 424804397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 424673325 424804397).card = 422 := join_1_0

end S202C08
end Sude.GeneratedTwinScan
