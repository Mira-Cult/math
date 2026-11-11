import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19058)) 363200557 363233325 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363200557 363233325).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19058 363200557 363233325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19059)) 363233325 363266093 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 363233325 363266093).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19059 363233325 363266093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19060)) 363266093 363298861 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363266093 363298861).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19060 363266093 363298861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19061)) 363298861 363331629 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363298861 363331629).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19061 363298861 363331629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363200557 363266093).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 363200557 ≤ 363233325)
    (by decide : 363233325 ≤ 363266093) block0 block1

theorem join_0_1 : (twinPrimeSegment 363266093 363331629).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 363266093 ≤ 363298861)
    (by decide : 363298861 ≤ 363331629) block2 block3

theorem join_1_0 : (twinPrimeSegment 363200557 363331629).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 363200557 ≤ 363266093)
    (by decide : 363266093 ≤ 363331629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363200557 363331629).card = 459 := join_1_0

end S173C03
end Sude.GeneratedTwinScan
