import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17219)) 296484909 296517677 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 296484909 296517677).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17219 296484909 296517677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17220)) 296517677 296550445 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 296517677 296550445).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17220 296517677 296550445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17221)) 296550445 296583213 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296550445 296583213).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17221 296550445 296583213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17222)) 296583213 296615981 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296583213 296615981).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17222 296583213 296615981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 296484909 296550445).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 296484909 ≤ 296517677)
    (by decide : 296517677 ≤ 296550445) block0 block1

theorem join_0_1 : (twinPrimeSegment 296550445 296615981).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 296550445 ≤ 296583213)
    (by decide : 296583213 ≤ 296615981) block2 block3

theorem join_1_0 : (twinPrimeSegment 296484909 296615981).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 296484909 ≤ 296550445)
    (by decide : 296550445 ≤ 296615981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 296484909 296615981).card = 436 := join_1_0

end S141C06
end Sude.GeneratedTwinScan
