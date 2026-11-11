import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22191)) 492437549 492470317 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492437549 492470317).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22191 492437549 492470317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22192)) 492470317 492503085 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492470317 492503085).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22192 492470317 492503085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22193)) 492503085 492535853 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 492503085 492535853).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22193 492503085 492535853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22193)) 492535853 492568621 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492535853 492568621).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22193 492535853 492568621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492437549 492503085).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 492437549 ≤ 492470317)
    (by decide : 492470317 ≤ 492503085) block0 block1

theorem join_0_1 : (twinPrimeSegment 492503085 492568621).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 492503085 ≤ 492535853)
    (by decide : 492535853 ≤ 492568621) block2 block3

theorem join_1_0 : (twinPrimeSegment 492437549 492568621).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 492437549 ≤ 492503085)
    (by decide : 492503085 ≤ 492568621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492437549 492568621).card = 428 := join_1_0

end S234C13
end Sude.GeneratedTwinScan
