import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20535)) 421658669 421691437 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421658669 421691437).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20535 421658669 421691437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20535)) 421691437 421724205 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421691437 421724205).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20535 421691437 421724205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20536)) 421724205 421756973 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421724205 421756973).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20536 421724205 421756973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20537)) 421756973 421789741 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 421756973 421789741).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20537 421756973 421789741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421658669 421724205).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 421658669 ≤ 421691437)
    (by decide : 421691437 ≤ 421724205) block0 block1

theorem join_0_1 : (twinPrimeSegment 421724205 421789741).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 421724205 ≤ 421756973)
    (by decide : 421756973 ≤ 421789741) block2 block3

theorem join_1_0 : (twinPrimeSegment 421658669 421789741).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 421658669 ≤ 421724205)
    (by decide : 421724205 ≤ 421789741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421658669 421789741).card = 439 := join_1_0

end S201C01
end Sude.GeneratedTwinScan
