import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14733)) 217055277 217088045 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217055277 217088045).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14733 217055277 217088045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14735)) 217088045 217120813 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 217088045 217120813).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14735 217088045 217120813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14736)) 217120813 217153581 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 217120813 217153581).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14736 217120813 217153581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14737)) 217153581 217186349 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217153581 217186349).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14737 217153581 217186349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217055277 217120813).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 217055277 ≤ 217088045)
    (by decide : 217088045 ≤ 217120813) block0 block1

theorem join_0_1 : (twinPrimeSegment 217120813 217186349).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 217120813 ≤ 217153581)
    (by decide : 217153581 ≤ 217186349) block2 block3

theorem join_1_0 : (twinPrimeSegment 217055277 217186349).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 217055277 ≤ 217120813)
    (by decide : 217120813 ≤ 217186349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217055277 217186349).card = 458 := join_1_0

end S103C08
end Sude.GeneratedTwinScan
