import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21951)) 481820717 481853485 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481820717 481853485).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21951 481820717 481853485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21951)) 481853485 481886253 = 79 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481853485 481886253).card = 79 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21951 481853485 481886253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21952)) 481886253 481919021 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 481886253 481919021).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21952 481886253 481919021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21953)) 481919021 481951789 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481919021 481951789).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21953 481919021 481951789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481820717 481886253).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 481820717 ≤ 481853485)
    (by decide : 481853485 ≤ 481886253) block0 block1

theorem join_0_1 : (twinPrimeSegment 481886253 481951789).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 481886253 ≤ 481919021)
    (by decide : 481919021 ≤ 481951789) block2 block3

theorem join_1_0 : (twinPrimeSegment 481820717 481951789).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 481820717 ≤ 481886253)
    (by decide : 481886253 ≤ 481951789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481820717 481951789).card = 411 := join_1_0

end S229C12
end Sude.GeneratedTwinScan
