import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18211)) 331612205 331644973 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 331612205 331644973).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18211 331612205 331644973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18212)) 331644973 331677741 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 331644973 331677741).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18212 331644973 331677741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18212)) 331677741 331710509 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 331677741 331710509).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18212 331677741 331710509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18213)) 331710509 331743277 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 331710509 331743277).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18213 331710509 331743277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 331612205 331677741).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 331612205 ≤ 331644973)
    (by decide : 331644973 ≤ 331677741) block0 block1

theorem join_0_1 : (twinPrimeSegment 331677741 331743277).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 331677741 ≤ 331710509)
    (by decide : 331710509 ≤ 331743277) block2 block3

theorem join_1_0 : (twinPrimeSegment 331612205 331743277).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 331612205 ≤ 331677741)
    (by decide : 331677741 ≤ 331743277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 331612205 331743277).card = 454 := join_1_0

end S158C02
end Sude.GeneratedTwinScan
