import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21169)) 448135213 448167981 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448135213 448167981).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21169 448135213 448167981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21170)) 448167981 448200749 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448167981 448200749).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21170 448167981 448200749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21171)) 448200749 448233517 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448200749 448233517).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21171 448200749 448233517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21172)) 448233517 448266285 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 448233517 448266285).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21172 448233517 448266285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448135213 448200749).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 448135213 ≤ 448167981)
    (by decide : 448167981 ≤ 448200749) block0 block1

theorem join_0_1 : (twinPrimeSegment 448200749 448266285).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 448200749 ≤ 448233517)
    (by decide : 448233517 ≤ 448266285) block2 block3

theorem join_1_0 : (twinPrimeSegment 448135213 448266285).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 448135213 ≤ 448200749)
    (by decide : 448200749 ≤ 448266285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448135213 448266285).card = 423 := join_1_0

end S213C11
end Sude.GeneratedTwinScan
