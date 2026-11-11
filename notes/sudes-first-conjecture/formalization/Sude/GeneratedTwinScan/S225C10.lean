import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21753)) 473169965 473202733 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 473169965 473202733).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21753 473169965 473202733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21753)) 473202733 473235501 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 473202733 473235501).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21753 473202733 473235501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21754)) 473235501 473268269 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 473235501 473268269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21754 473235501 473268269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21755)) 473268269 473301037 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 473268269 473301037).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21755 473268269 473301037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 473169965 473235501).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 473169965 ≤ 473202733)
    (by decide : 473202733 ≤ 473235501) block0 block1

theorem join_0_1 : (twinPrimeSegment 473235501 473301037).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 473235501 ≤ 473268269)
    (by decide : 473268269 ≤ 473301037) block2 block3

theorem join_1_0 : (twinPrimeSegment 473169965 473301037).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 473169965 ≤ 473235501)
    (by decide : 473235501 ≤ 473301037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 473169965 473301037).card = 445 := join_1_0

end S225C10
end Sude.GeneratedTwinScan
