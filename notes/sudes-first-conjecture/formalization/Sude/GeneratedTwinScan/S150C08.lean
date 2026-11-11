import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17766)) 315621421 315654189 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 315621421 315654189).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17766 315621421 315654189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17767)) 315654189 315686957 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 315654189 315686957).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17767 315654189 315686957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17768)) 315686957 315719725 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 315686957 315719725).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17768 315686957 315719725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17769)) 315719725 315752493 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 315719725 315752493).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17769 315719725 315752493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 315621421 315686957).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 315621421 ≤ 315654189)
    (by decide : 315654189 ≤ 315686957) block0 block1

theorem join_0_1 : (twinPrimeSegment 315686957 315752493).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 315686957 ≤ 315719725)
    (by decide : 315719725 ≤ 315752493) block2 block3

theorem join_1_0 : (twinPrimeSegment 315621421 315752493).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 315621421 ≤ 315686957)
    (by decide : 315686957 ≤ 315752493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 315621421 315752493).card = 460 := join_1_0

end S150C08
end Sude.GeneratedTwinScan
