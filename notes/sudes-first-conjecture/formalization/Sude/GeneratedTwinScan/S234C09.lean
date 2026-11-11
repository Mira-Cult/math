import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22179)) 491913261 491946029 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 491913261 491946029).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22179 491913261 491946029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22180)) 491946029 491978797 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 491946029 491978797).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22180 491946029 491978797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22181)) 491978797 492011565 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 491978797 492011565).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22181 491978797 492011565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22182)) 492011565 492044333 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492011565 492044333).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22182 492011565 492044333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 491913261 491978797).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 491913261 ≤ 491946029)
    (by decide : 491946029 ≤ 491978797) block0 block1

theorem join_0_1 : (twinPrimeSegment 491978797 492044333).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 491978797 ≤ 492011565)
    (by decide : 492011565 ≤ 492044333) block2 block3

theorem join_1_0 : (twinPrimeSegment 491913261 492044333).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 491913261 ≤ 491978797)
    (by decide : 491978797 ≤ 492044333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 491913261 492044333).card = 443 := join_1_0

end S234C09
end Sude.GeneratedTwinScan
