import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14450)) 208797741 208830509 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 208797741 208830509).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14450 208797741 208830509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14452)) 208830509 208863277 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 208830509 208863277).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14452 208830509 208863277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14453)) 208863277 208896045 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 208863277 208896045).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14453 208863277 208896045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14454)) 208896045 208928813 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 208896045 208928813).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14454 208896045 208928813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 208797741 208863277).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 208797741 ≤ 208830509)
    (by decide : 208830509 ≤ 208863277) block0 block1

theorem join_0_1 : (twinPrimeSegment 208863277 208928813).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 208863277 ≤ 208896045)
    (by decide : 208896045 ≤ 208928813) block2 block3

theorem join_1_0 : (twinPrimeSegment 208797741 208928813).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 208797741 ≤ 208863277)
    (by decide : 208863277 ≤ 208928813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 208797741 208928813).card = 509 := join_1_0

end S099C09
end Sude.GeneratedTwinScan
