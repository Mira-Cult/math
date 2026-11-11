import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21234)) 450887725 450920493 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 450887725 450920493).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21234 450887725 450920493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21235)) 450920493 450953261 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 450920493 450953261).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21235 450920493 450953261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21236)) 450953261 450986029 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 450953261 450986029).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21236 450953261 450986029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21237)) 450986029 451018797 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 450986029 451018797).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21237 450986029 451018797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 450887725 450953261).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 450887725 ≤ 450920493)
    (by decide : 450920493 ≤ 450953261) block0 block1

theorem join_0_1 : (twinPrimeSegment 450953261 451018797).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 450953261 ≤ 450986029)
    (by decide : 450986029 ≤ 451018797) block2 block3

theorem join_1_0 : (twinPrimeSegment 450887725 451018797).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 450887725 ≤ 450953261)
    (by decide : 450953261 ≤ 451018797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 450887725 451018797).card = 445 := join_1_0

end S215C00
end Sude.GeneratedTwinScan
