import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19856)) 394264621 394297389 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394264621 394297389).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19856 394264621 394297389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19857)) 394297389 394330157 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394297389 394330157).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19857 394297389 394330157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19858)) 394330157 394362925 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394330157 394362925).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19858 394330157 394362925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19859)) 394362925 394395693 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 394362925 394395693).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19859 394362925 394395693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394264621 394330157).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 394297389)
    (by decide : 394297389 ≤ 394330157) block0 block1

theorem join_0_1 : (twinPrimeSegment 394330157 394395693).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 394330157 ≤ 394362925)
    (by decide : 394362925 ≤ 394395693) block2 block3

theorem join_1_0 : (twinPrimeSegment 394264621 394395693).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 394330157)
    (by decide : 394330157 ≤ 394395693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394264621 394395693).card = 434 := join_1_0

end S188C00
end Sude.GeneratedTwinScan
