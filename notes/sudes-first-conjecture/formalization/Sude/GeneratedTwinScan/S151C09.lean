import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17829)) 317849645 317882413 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 317849645 317882413).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17829 317849645 317882413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17830)) 317882413 317915181 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 317882413 317915181).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17830 317882413 317915181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17831)) 317915181 317947949 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 317915181 317947949).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17831 317915181 317947949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17832)) 317947949 317980717 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 317947949 317980717).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17832 317947949 317980717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 317849645 317915181).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 317849645 ≤ 317882413)
    (by decide : 317882413 ≤ 317915181) block0 block1

theorem join_0_1 : (twinPrimeSegment 317915181 317980717).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 317915181 ≤ 317947949)
    (by decide : 317947949 ≤ 317980717) block2 block3

theorem join_1_0 : (twinPrimeSegment 317849645 317980717).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 317849645 ≤ 317915181)
    (by decide : 317915181 ≤ 317980717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 317849645 317980717).card = 458 := join_1_0

end S151C09
end Sude.GeneratedTwinScan
