import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16583)) 274989101 275021869 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274989101 275021869).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16583 274989101 275021869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16584)) 275021869 275054637 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 275021869 275054637).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16584 275021869 275054637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16585)) 275054637 275087405 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 275054637 275087405).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16585 275054637 275087405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16586)) 275087405 275120173 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 275087405 275120173).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16586 275087405 275120173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274989101 275054637).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 274989101 ≤ 275021869)
    (by decide : 275021869 ≤ 275054637) block0 block1

theorem join_0_1 : (twinPrimeSegment 275054637 275120173).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 275054637 ≤ 275087405)
    (by decide : 275087405 ≤ 275120173) block2 block3

theorem join_1_0 : (twinPrimeSegment 274989101 275120173).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 274989101 ≤ 275054637)
    (by decide : 275054637 ≤ 275120173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274989101 275120173).card = 427 := join_1_0

end S131C02
end Sude.GeneratedTwinScan
