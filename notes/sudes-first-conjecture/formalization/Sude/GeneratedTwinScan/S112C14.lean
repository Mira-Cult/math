import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15386)) 236716077 236748845 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 236716077 236748845).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15386 236716077 236748845
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15387)) 236748845 236781613 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 236748845 236781613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15387 236748845 236781613
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15388)) 236781613 236814381 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 236781613 236814381).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15388 236781613 236814381
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15389)) 236814381 236847149 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 236814381 236847149).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15389 236814381 236847149
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 236716077 236781613).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 236716077 ≤ 236748845)
    (by decide : 236748845 ≤ 236781613) block0 block1

theorem join_0_1 : (twinPrimeSegment 236781613 236847149).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 236781613 ≤ 236814381)
    (by decide : 236814381 ≤ 236847149) block2 block3

theorem join_1_0 : (twinPrimeSegment 236716077 236847149).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 236716077 ≤ 236781613)
    (by decide : 236781613 ≤ 236847149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 236716077 236847149).card = 454 := join_1_0

end S112C14
end Sude.GeneratedTwinScan
