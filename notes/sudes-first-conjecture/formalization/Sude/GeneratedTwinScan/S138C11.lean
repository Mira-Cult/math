import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17055)) 290848813 290881581 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290848813 290881581).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17055 290848813 290881581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17056)) 290881581 290914349 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 290881581 290914349).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17056 290881581 290914349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17057)) 290914349 290947117 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 290914349 290947117).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17057 290914349 290947117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17058)) 290947117 290979885 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290947117 290979885).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17058 290947117 290979885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290848813 290914349).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 290848813 ≤ 290881581)
    (by decide : 290881581 ≤ 290914349) block0 block1

theorem join_0_1 : (twinPrimeSegment 290914349 290979885).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 290914349 ≤ 290947117)
    (by decide : 290947117 ≤ 290979885) block2 block3

theorem join_1_0 : (twinPrimeSegment 290848813 290979885).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 290848813 ≤ 290914349)
    (by decide : 290914349 ≤ 290979885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290848813 290979885).card = 466 := join_1_0

end S138C11
end Sude.GeneratedTwinScan
