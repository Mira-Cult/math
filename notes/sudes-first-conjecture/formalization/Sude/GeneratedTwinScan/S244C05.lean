import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22636)) 512360493 512393261 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 512360493 512393261).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22636 512360493 512393261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22636)) 512393261 512426029 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 512393261 512426029).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22636 512393261 512426029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22637)) 512426029 512458797 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 512426029 512458797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22637 512426029 512458797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22638)) 512458797 512491565 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 512458797 512491565).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22638 512458797 512491565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 512360493 512426029).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 512360493 ≤ 512393261)
    (by decide : 512393261 ≤ 512426029) block0 block1

theorem join_0_1 : (twinPrimeSegment 512426029 512491565).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 512426029 ≤ 512458797)
    (by decide : 512458797 ≤ 512491565) block2 block3

theorem join_1_0 : (twinPrimeSegment 512360493 512491565).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 512360493 ≤ 512426029)
    (by decide : 512426029 ≤ 512491565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 512360493 512491565).card = 418 := join_1_0

end S244C05
end Sude.GeneratedTwinScan
