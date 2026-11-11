import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14203)) 201719853 201752621 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 201719853 201752621).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14203 201719853 201752621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14205)) 201752621 201785389 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 201752621 201785389).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14205 201752621 201785389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14206)) 201785389 201818157 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 201785389 201818157).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14206 201785389 201818157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14207)) 201818157 201850925 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 201818157 201850925).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14207 201818157 201850925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 201719853 201785389).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 201719853 ≤ 201752621)
    (by decide : 201752621 ≤ 201785389) block0 block1

theorem join_0_1 : (twinPrimeSegment 201785389 201850925).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 201785389 ≤ 201818157)
    (by decide : 201818157 ≤ 201850925) block2 block3

theorem join_1_0 : (twinPrimeSegment 201719853 201850925).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 201719853 ≤ 201785389)
    (by decide : 201785389 ≤ 201850925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 201719853 201850925).card = 461 := join_1_0

end S096C03
end Sude.GeneratedTwinScan
