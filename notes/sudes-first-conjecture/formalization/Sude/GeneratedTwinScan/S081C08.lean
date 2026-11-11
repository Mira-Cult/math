import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13074)) 170917933 170950701 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 170917933 170950701).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13074 170917933 170950701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13076)) 170950701 170983469 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 170950701 170983469).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13076 170950701 170983469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13077)) 170983469 171016237 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 170983469 171016237).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13077 170983469 171016237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13078)) 171016237 171049005 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 171016237 171049005).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13078 171016237 171049005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 170917933 170983469).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 170917933 ≤ 170950701)
    (by decide : 170950701 ≤ 170983469) block0 block1

theorem join_0_1 : (twinPrimeSegment 170983469 171049005).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 170983469 ≤ 171016237)
    (by decide : 171016237 ≤ 171049005) block2 block3

theorem join_1_0 : (twinPrimeSegment 170917933 171049005).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 170917933 ≤ 170983469)
    (by decide : 170983469 ≤ 171049005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 170917933 171049005).card = 506 := join_1_0

end S081C08
end Sude.GeneratedTwinScan
