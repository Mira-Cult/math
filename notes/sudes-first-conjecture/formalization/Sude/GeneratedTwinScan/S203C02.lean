import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20640)) 425984045 426016813 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 425984045 426016813).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20640 425984045 426016813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20640)) 426016813 426049581 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 426016813 426049581).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20640 426016813 426049581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20641)) 426049581 426082349 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 426049581 426082349).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20641 426049581 426082349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20642)) 426082349 426115117 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 426082349 426115117).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20642 426082349 426115117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 425984045 426049581).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 425984045 ≤ 426016813)
    (by decide : 426016813 ≤ 426049581) block0 block1

theorem join_0_1 : (twinPrimeSegment 426049581 426115117).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 426049581 ≤ 426082349)
    (by decide : 426082349 ≤ 426115117) block2 block3

theorem join_1_0 : (twinPrimeSegment 425984045 426115117).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 425984045 ≤ 426049581)
    (by decide : 426049581 ≤ 426115117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 425984045 426115117).card = 448 := join_1_0

end S203C02
end Sude.GeneratedTwinScan
