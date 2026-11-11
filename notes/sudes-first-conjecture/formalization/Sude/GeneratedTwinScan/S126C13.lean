import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16308)) 265945133 265977901 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 265945133 265977901).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16308 265945133 265977901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16309)) 265977901 266010669 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 265977901 266010669).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16309 265977901 266010669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16310)) 266010669 266043437 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 266010669 266043437).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16310 266010669 266043437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16311)) 266043437 266076205 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 266043437 266076205).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16311 266043437 266076205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 265945133 266010669).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 265945133 ≤ 265977901)
    (by decide : 265977901 ≤ 266010669) block0 block1

theorem join_0_1 : (twinPrimeSegment 266010669 266076205).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 266010669 ≤ 266043437)
    (by decide : 266043437 ≤ 266076205) block2 block3

theorem join_1_0 : (twinPrimeSegment 265945133 266076205).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 265945133 ≤ 266010669)
    (by decide : 266010669 ≤ 266076205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 265945133 266076205).card = 477 := join_1_0

end S126C13
end Sude.GeneratedTwinScan
