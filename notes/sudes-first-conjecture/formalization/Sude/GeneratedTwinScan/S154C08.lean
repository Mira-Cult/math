import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18001)) 324010029 324042797 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324010029 324042797).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18001 324010029 324042797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18002)) 324042797 324075565 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324042797 324075565).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18002 324042797 324075565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18003)) 324075565 324108333 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324075565 324108333).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18003 324075565 324108333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18003)) 324108333 324141101 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 324108333 324141101).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18003 324108333 324141101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324010029 324075565).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 324010029 ≤ 324042797)
    (by decide : 324042797 ≤ 324075565) block0 block1

theorem join_0_1 : (twinPrimeSegment 324075565 324141101).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 324075565 ≤ 324108333)
    (by decide : 324108333 ≤ 324141101) block2 block3

theorem join_1_0 : (twinPrimeSegment 324010029 324141101).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 324010029 ≤ 324075565)
    (by decide : 324075565 ≤ 324141101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324010029 324141101).card = 451 := join_1_0

end S154C08
end Sude.GeneratedTwinScan
