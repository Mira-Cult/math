import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18171)) 330170413 330203181 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 330170413 330203181).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18171 330170413 330203181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18172)) 330203181 330235949 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 330203181 330235949).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18172 330203181 330235949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18173)) 330235949 330268717 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 330235949 330268717).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18173 330235949 330268717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18174)) 330268717 330301485 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 330268717 330301485).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18174 330268717 330301485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 330170413 330235949).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 330170413 ≤ 330203181)
    (by decide : 330203181 ≤ 330235949) block0 block1

theorem join_0_1 : (twinPrimeSegment 330235949 330301485).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 330235949 ≤ 330268717)
    (by decide : 330268717 ≤ 330301485) block2 block3

theorem join_1_0 : (twinPrimeSegment 330170413 330301485).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 330170413 ≤ 330235949)
    (by decide : 330235949 ≤ 330301485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 330170413 330301485).card = 426 := join_1_0

end S157C07
end Sude.GeneratedTwinScan
