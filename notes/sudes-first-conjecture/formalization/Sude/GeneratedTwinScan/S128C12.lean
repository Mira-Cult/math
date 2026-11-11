import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16432)) 270008365 270041133 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 270008365 270041133).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16432 270008365 270041133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16433)) 270041133 270073901 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 270041133 270073901).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16433 270041133 270073901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16434)) 270073901 270106669 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 270073901 270106669).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16434 270073901 270106669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16435)) 270106669 270139437 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 270106669 270139437).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16435 270106669 270139437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 270008365 270073901).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 270008365 ≤ 270041133)
    (by decide : 270041133 ≤ 270073901) block0 block1

theorem join_0_1 : (twinPrimeSegment 270073901 270139437).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 270073901 ≤ 270106669)
    (by decide : 270106669 ≤ 270139437) block2 block3

theorem join_1_0 : (twinPrimeSegment 270008365 270139437).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 270008365 ≤ 270073901)
    (by decide : 270073901 ≤ 270139437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 270008365 270139437).card = 465 := join_1_0

end S128C12
end Sude.GeneratedTwinScan
