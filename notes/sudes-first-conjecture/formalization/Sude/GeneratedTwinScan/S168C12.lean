import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18812)) 353894445 353927213 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 353894445 353927213).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18812 353894445 353927213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18813)) 353927213 353959981 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353927213 353959981).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18813 353927213 353959981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18814)) 353959981 353992749 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353959981 353992749).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18814 353959981 353992749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18815)) 353992749 354025517 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353992749 354025517).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18815 353992749 354025517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 353894445 353959981).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 353894445 ≤ 353927213)
    (by decide : 353927213 ≤ 353959981) block0 block1

theorem join_0_1 : (twinPrimeSegment 353959981 354025517).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 353959981 ≤ 353992749)
    (by decide : 353992749 ≤ 354025517) block2 block3

theorem join_1_0 : (twinPrimeSegment 353894445 354025517).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 353894445 ≤ 353959981)
    (by decide : 353959981 ≤ 354025517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 353894445 354025517).card = 438 := join_1_0

end S168C12
end Sude.GeneratedTwinScan
