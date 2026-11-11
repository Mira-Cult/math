import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22073)) 487194669 487227437 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487194669 487227437).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22073 487194669 487227437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22073)) 487227437 487260205 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 487227437 487260205).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22073 487227437 487260205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22074)) 487260205 487292973 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 487260205 487292973).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22074 487260205 487292973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22075)) 487292973 487325741 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487292973 487325741).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22075 487292973 487325741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487194669 487260205).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 487194669 ≤ 487227437)
    (by decide : 487227437 ≤ 487260205) block0 block1

theorem join_0_1 : (twinPrimeSegment 487260205 487325741).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 487260205 ≤ 487292973)
    (by decide : 487292973 ≤ 487325741) block2 block3

theorem join_1_0 : (twinPrimeSegment 487194669 487325741).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 487194669 ≤ 487260205)
    (by decide : 487260205 ≤ 487325741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487194669 487325741).card = 432 := join_1_0

end S232C05
end Sude.GeneratedTwinScan
