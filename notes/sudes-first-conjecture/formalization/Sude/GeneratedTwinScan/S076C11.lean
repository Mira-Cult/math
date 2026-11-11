import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12682)) 160825389 160858157 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 160825389 160858157).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12682 160825389 160858157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12684)) 160858157 160890925 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 160858157 160890925).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12684 160858157 160890925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12685)) 160890925 160923693 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 160890925 160923693).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12685 160890925 160923693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12686)) 160923693 160956461 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160923693 160956461).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12686 160923693 160956461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 160825389 160890925).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 160825389 ≤ 160858157)
    (by decide : 160858157 ≤ 160890925) block0 block1

theorem join_0_1 : (twinPrimeSegment 160890925 160956461).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 160890925 ≤ 160923693)
    (by decide : 160923693 ≤ 160956461) block2 block3

theorem join_1_0 : (twinPrimeSegment 160825389 160956461).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 160825389 ≤ 160890925)
    (by decide : 160890925 ≤ 160956461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 160825389 160956461).card = 464 := join_1_0

end S076C11
end Sude.GeneratedTwinScan
