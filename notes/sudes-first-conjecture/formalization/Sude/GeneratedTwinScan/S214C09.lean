import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21213)) 449970221 450002989 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449970221 450002989).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21213 449970221 450002989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21214)) 450002989 450035757 = 88 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 450002989 450035757).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21214 450002989 450035757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21214)) 450035757 450068525 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 450035757 450068525).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21214 450035757 450068525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21215)) 450068525 450101293 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 450068525 450101293).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21215 450068525 450101293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449970221 450035757).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 449970221 ≤ 450002989)
    (by decide : 450002989 ≤ 450035757) block0 block1

theorem join_0_1 : (twinPrimeSegment 450035757 450101293).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 450035757 ≤ 450068525)
    (by decide : 450068525 ≤ 450101293) block2 block3

theorem join_1_0 : (twinPrimeSegment 449970221 450101293).card = 395 := by
  simpa using combineTwinPrimeSegments (by decide : 449970221 ≤ 450035757)
    (by decide : 450035757 ≤ 450101293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449970221 450101293).card = 395 := join_1_0

end S214C09
end Sude.GeneratedTwinScan
