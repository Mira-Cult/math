import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16276)) 264896557 264929325 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 264896557 264929325).card = 143 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16276 264896557 264929325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16277)) 264929325 264962093 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264929325 264962093).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16277 264929325 264962093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16278)) 264962093 264994861 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264962093 264994861).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16278 264962093 264994861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16279)) 264994861 265027629 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264994861 265027629).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16279 264994861 265027629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 264896557 264962093).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 264896557 ≤ 264929325)
    (by decide : 264929325 ≤ 264962093) block0 block1

theorem join_0_1 : (twinPrimeSegment 264962093 265027629).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 264962093 ≤ 264994861)
    (by decide : 264994861 ≤ 265027629) block2 block3

theorem join_1_0 : (twinPrimeSegment 264896557 265027629).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 264896557 ≤ 264962093)
    (by decide : 264962093 ≤ 265027629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 264896557 265027629).card = 480 := join_1_0

end S126C05
end Sude.GeneratedTwinScan
