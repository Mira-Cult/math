import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16709)) 279183405 279216173 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 279183405 279216173).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16709 279183405 279216173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16710)) 279216173 279248941 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 279216173 279248941).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16710 279216173 279248941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16711)) 279248941 279281709 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 279248941 279281709).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16711 279248941 279281709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16712)) 279281709 279314477 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 279281709 279314477).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16712 279281709 279314477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 279183405 279248941).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 279183405 ≤ 279216173)
    (by decide : 279216173 ≤ 279248941) block0 block1

theorem join_0_1 : (twinPrimeSegment 279248941 279314477).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 279248941 ≤ 279281709)
    (by decide : 279281709 ≤ 279314477) block2 block3

theorem join_1_0 : (twinPrimeSegment 279183405 279314477).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 279183405 ≤ 279248941)
    (by decide : 279248941 ≤ 279314477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 279183405 279314477).card = 450 := join_1_0

end S133C02
end Sude.GeneratedTwinScan
