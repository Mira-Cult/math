import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16846)) 283770925 283803693 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 283770925 283803693).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16846 283770925 283803693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16847)) 283803693 283836461 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283803693 283836461).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16847 283803693 283836461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16848)) 283836461 283869229 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283836461 283869229).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16848 283836461 283869229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16849)) 283869229 283901997 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 283869229 283901997).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16849 283869229 283901997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 283770925 283836461).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 283770925 ≤ 283803693)
    (by decide : 283803693 ≤ 283836461) block0 block1

theorem join_0_1 : (twinPrimeSegment 283836461 283901997).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 283836461 ≤ 283869229)
    (by decide : 283869229 ≤ 283901997) block2 block3

theorem join_1_0 : (twinPrimeSegment 283770925 283901997).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 283770925 ≤ 283836461)
    (by decide : 283836461 ≤ 283901997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 283770925 283901997).card = 479 := join_1_0

end S135C05
end Sude.GeneratedTwinScan
