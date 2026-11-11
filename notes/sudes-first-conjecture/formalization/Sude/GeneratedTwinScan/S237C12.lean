import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22330)) 498597933 498630701 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 498597933 498630701).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22330 498597933 498630701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22330)) 498630701 498663469 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 498630701 498663469).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22330 498630701 498663469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22331)) 498663469 498696237 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498663469 498696237).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22331 498663469 498696237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22332)) 498696237 498729005 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498696237 498729005).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22332 498696237 498729005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 498597933 498663469).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 498597933 ≤ 498630701)
    (by decide : 498630701 ≤ 498663469) block0 block1

theorem join_0_1 : (twinPrimeSegment 498663469 498729005).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 498663469 ≤ 498696237)
    (by decide : 498696237 ≤ 498729005) block2 block3

theorem join_1_0 : (twinPrimeSegment 498597933 498729005).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 498597933 ≤ 498663469)
    (by decide : 498663469 ≤ 498729005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 498597933 498729005).card = 416 := join_1_0

end S237C12
end Sude.GeneratedTwinScan
