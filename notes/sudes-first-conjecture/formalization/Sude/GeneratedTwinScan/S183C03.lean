import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19601)) 384172077 384204845 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 384172077 384204845).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19601 384172077 384204845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19601)) 384204845 384237613 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 384204845 384237613).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19601 384204845 384237613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19602)) 384237613 384270381 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 384237613 384270381).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19602 384237613 384270381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19603)) 384270381 384303149 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 384270381 384303149).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19603 384270381 384303149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 384172077 384237613).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 384172077 ≤ 384204845)
    (by decide : 384204845 ≤ 384237613) block0 block1

theorem join_0_1 : (twinPrimeSegment 384237613 384303149).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 384237613 ≤ 384270381)
    (by decide : 384270381 ≤ 384303149) block2 block3

theorem join_1_0 : (twinPrimeSegment 384172077 384303149).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 384172077 ≤ 384237613)
    (by decide : 384237613 ≤ 384303149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 384172077 384303149).card = 464 := join_1_0

end S183C03
end Sude.GeneratedTwinScan
