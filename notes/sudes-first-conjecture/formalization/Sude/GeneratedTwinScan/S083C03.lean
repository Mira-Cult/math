import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13209)) 174456877 174489645 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 174456877 174489645).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13209 174456877 174489645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13210)) 174489645 174522413 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 174489645 174522413).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13210 174489645 174522413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13211)) 174522413 174555181 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 174522413 174555181).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13211 174522413 174555181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13213)) 174555181 174587949 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 174555181 174587949).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13213 174555181 174587949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 174456877 174522413).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 174456877 ≤ 174489645)
    (by decide : 174489645 ≤ 174522413) block0 block1

theorem join_0_1 : (twinPrimeSegment 174522413 174587949).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 174522413 ≤ 174555181)
    (by decide : 174555181 ≤ 174587949) block2 block3

theorem join_1_0 : (twinPrimeSegment 174456877 174587949).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 174456877 ≤ 174522413)
    (by decide : 174522413 ≤ 174587949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 174456877 174587949).card = 490 := join_1_0

end S083C03
end Sude.GeneratedTwinScan
