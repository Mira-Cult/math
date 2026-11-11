import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14950)) 223477805 223510573 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 223477805 223510573).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14950 223477805 223510573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14951)) 223510573 223543341 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 223510573 223543341).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14951 223510573 223543341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14952)) 223543341 223576109 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 223543341 223576109).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14952 223543341 223576109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14953)) 223576109 223608877 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 223576109 223608877).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14953 223576109 223608877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 223477805 223543341).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 223477805 ≤ 223510573)
    (by decide : 223510573 ≤ 223543341) block0 block1

theorem join_0_1 : (twinPrimeSegment 223543341 223608877).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 223543341 ≤ 223576109)
    (by decide : 223576109 ≤ 223608877) block2 block3

theorem join_1_0 : (twinPrimeSegment 223477805 223608877).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 223477805 ≤ 223543341)
    (by decide : 223543341 ≤ 223608877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 223477805 223608877).card = 485 := join_1_0

end S106C09
end Sude.GeneratedTwinScan
