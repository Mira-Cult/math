import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15815)) 250085421 250118189 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 250085421 250118189).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15815 250085421 250118189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15816)) 250118189 250150957 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 250118189 250150957).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15816 250118189 250150957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15817)) 250150957 250183725 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250150957 250183725).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15817 250150957 250183725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15818)) 250183725 250216493 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250183725 250216493).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15818 250183725 250216493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 250085421 250150957).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 250085421 ≤ 250118189)
    (by decide : 250118189 ≤ 250150957) block0 block1

theorem join_0_1 : (twinPrimeSegment 250150957 250216493).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 250150957 ≤ 250183725)
    (by decide : 250183725 ≤ 250216493) block2 block3

theorem join_1_0 : (twinPrimeSegment 250085421 250216493).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 250085421 ≤ 250150957)
    (by decide : 250150957 ≤ 250216493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 250085421 250216493).card = 479 := join_1_0

end S119C04
end Sude.GeneratedTwinScan
