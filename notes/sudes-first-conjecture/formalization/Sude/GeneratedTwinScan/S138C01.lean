import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17016)) 289538093 289570861 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 289538093 289570861).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17016 289538093 289570861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17017)) 289570861 289603629 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 289570861 289603629).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17017 289570861 289603629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17018)) 289603629 289636397 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 289603629 289636397).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17018 289603629 289636397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17019)) 289636397 289669165 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 289636397 289669165).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17019 289636397 289669165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 289538093 289603629).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 289538093 ≤ 289570861)
    (by decide : 289570861 ≤ 289603629) block0 block1

theorem join_0_1 : (twinPrimeSegment 289603629 289669165).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 289603629 ≤ 289636397)
    (by decide : 289636397 ≤ 289669165) block2 block3

theorem join_1_0 : (twinPrimeSegment 289538093 289669165).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 289538093 ≤ 289603629)
    (by decide : 289603629 ≤ 289669165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 289538093 289669165).card = 464 := join_1_0

end S138C01
end Sude.GeneratedTwinScan
