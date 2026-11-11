import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17599)) 309723181 309755949 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 309723181 309755949).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17599 309723181 309755949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17600)) 309755949 309788717 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 309755949 309788717).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17600 309755949 309788717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17601)) 309788717 309821485 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 309788717 309821485).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17601 309788717 309821485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17602)) 309821485 309854253 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 309821485 309854253).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17602 309821485 309854253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 309723181 309788717).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 309723181 ≤ 309755949)
    (by decide : 309755949 ≤ 309788717) block0 block1

theorem join_0_1 : (twinPrimeSegment 309788717 309854253).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 309788717 ≤ 309821485)
    (by decide : 309821485 ≤ 309854253) block2 block3

theorem join_1_0 : (twinPrimeSegment 309723181 309854253).card = 400 := by
  simpa using combineTwinPrimeSegments (by decide : 309723181 ≤ 309788717)
    (by decide : 309788717 ≤ 309854253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 309723181 309854253).card = 400 := join_1_0

end S147C11
end Sude.GeneratedTwinScan
