import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16931)) 286654509 286687277 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 286654509 286687277).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16931 286654509 286687277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16932)) 286687277 286720045 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286687277 286720045).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16932 286687277 286720045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16933)) 286720045 286752813 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286720045 286752813).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16933 286720045 286752813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16934)) 286752813 286785581 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 286752813 286785581).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16934 286752813 286785581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 286654509 286720045).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 286654509 ≤ 286687277)
    (by decide : 286687277 ≤ 286720045) block0 block1

theorem join_0_1 : (twinPrimeSegment 286720045 286785581).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 286720045 ≤ 286752813)
    (by decide : 286752813 ≤ 286785581) block2 block3

theorem join_1_0 : (twinPrimeSegment 286654509 286785581).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 286654509 ≤ 286720045)
    (by decide : 286720045 ≤ 286785581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 286654509 286785581).card = 438 := join_1_0

end S136C11
end Sude.GeneratedTwinScan
