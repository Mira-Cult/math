import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19318)) 373162029 373194797 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373162029 373194797).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19318 373162029 373194797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19319)) 373194797 373227565 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373194797 373227565).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19319 373194797 373227565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19319)) 373227565 373260333 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 373227565 373260333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19319 373227565 373260333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19320)) 373260333 373293101 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 373260333 373293101).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19320 373260333 373293101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373162029 373227565).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 373162029 ≤ 373194797)
    (by decide : 373194797 ≤ 373227565) block0 block1

theorem join_0_1 : (twinPrimeSegment 373227565 373293101).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 373227565 ≤ 373260333)
    (by decide : 373260333 ≤ 373293101) block2 block3

theorem join_1_0 : (twinPrimeSegment 373162029 373293101).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 373162029 ≤ 373227565)
    (by decide : 373227565 ≤ 373293101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373162029 373293101).card = 441 := join_1_0

end S177C15
end Sude.GeneratedTwinScan
