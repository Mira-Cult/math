import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22589)) 510263341 510296109 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 510263341 510296109).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22589 510263341 510296109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22590)) 510296109 510328877 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 510296109 510328877).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22590 510296109 510328877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22591)) 510328877 510361645 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 510328877 510361645).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22591 510328877 510361645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22591)) 510361645 510394413 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 510361645 510394413).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22591 510361645 510394413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 510263341 510328877).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 510263341 ≤ 510296109)
    (by decide : 510296109 ≤ 510328877) block0 block1

theorem join_0_1 : (twinPrimeSegment 510328877 510394413).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 510328877 ≤ 510361645)
    (by decide : 510361645 ≤ 510394413) block2 block3

theorem join_1_0 : (twinPrimeSegment 510263341 510394413).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 510263341 ≤ 510328877)
    (by decide : 510328877 ≤ 510394413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 510263341 510394413).card = 467 := join_1_0

end S243C05
end Sude.GeneratedTwinScan
