import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18669)) 348520493 348553261 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 348520493 348553261).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18669 348520493 348553261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18670)) 348553261 348586029 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348553261 348586029).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18670 348553261 348586029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18671)) 348586029 348618797 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348586029 348618797).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18671 348586029 348618797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18672)) 348618797 348651565 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 348618797 348651565).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18672 348618797 348651565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 348520493 348586029).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 348520493 ≤ 348553261)
    (by decide : 348553261 ≤ 348586029) block0 block1

theorem join_0_1 : (twinPrimeSegment 348586029 348651565).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 348586029 ≤ 348618797)
    (by decide : 348618797 ≤ 348651565) block2 block3

theorem join_1_0 : (twinPrimeSegment 348520493 348651565).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 348520493 ≤ 348586029)
    (by decide : 348586029 ≤ 348651565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 348520493 348651565).card = 425 := join_1_0

end S166C03
end Sude.GeneratedTwinScan
