import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18837)) 354811949 354844717 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 354811949 354844717).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18837 354811949 354844717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18838)) 354844717 354877485 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 354844717 354877485).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18838 354844717 354877485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18839)) 354877485 354910253 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 354877485 354910253).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18839 354877485 354910253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18839)) 354910253 354943021 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 354910253 354943021).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18839 354910253 354943021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 354811949 354877485).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 354811949 ≤ 354844717)
    (by decide : 354844717 ≤ 354877485) block0 block1

theorem join_0_1 : (twinPrimeSegment 354877485 354943021).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 354877485 ≤ 354910253)
    (by decide : 354910253 ≤ 354943021) block2 block3

theorem join_1_0 : (twinPrimeSegment 354811949 354943021).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 354811949 ≤ 354877485)
    (by decide : 354877485 ≤ 354943021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 354811949 354943021).card = 410 := join_1_0

end S169C03
end Sude.GeneratedTwinScan
