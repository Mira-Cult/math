import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14729)) 216924205 216956973 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 216924205 216956973).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14729 216924205 216956973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14730)) 216956973 216989741 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 216956973 216989741).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14730 216956973 216989741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14731)) 216989741 217022509 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 216989741 217022509).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14731 216989741 217022509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14732)) 217022509 217055277 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217022509 217055277).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14732 217022509 217055277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 216924205 216989741).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 216924205 ≤ 216956973)
    (by decide : 216956973 ≤ 216989741) block0 block1

theorem join_0_1 : (twinPrimeSegment 216989741 217055277).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 216989741 ≤ 217022509)
    (by decide : 217022509 ≤ 217055277) block2 block3

theorem join_1_0 : (twinPrimeSegment 216924205 217055277).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 216924205 ≤ 216989741)
    (by decide : 216989741 ≤ 217055277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 216924205 217055277).card = 493 := join_1_0

end S103C07
end Sude.GeneratedTwinScan
