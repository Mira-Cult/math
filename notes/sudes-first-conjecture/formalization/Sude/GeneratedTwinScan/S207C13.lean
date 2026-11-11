import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20876)) 435814445 435847213 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 435814445 435847213).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20876 435814445 435847213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20877)) 435847213 435879981 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 435847213 435879981).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20877 435847213 435879981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20878)) 435879981 435912749 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 435879981 435912749).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20878 435879981 435912749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20879)) 435912749 435945517 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 435912749 435945517).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20879 435912749 435945517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 435814445 435879981).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 435814445 ≤ 435847213)
    (by decide : 435847213 ≤ 435879981) block0 block1

theorem join_0_1 : (twinPrimeSegment 435879981 435945517).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 435879981 ≤ 435912749)
    (by decide : 435912749 ≤ 435945517) block2 block3

theorem join_1_0 : (twinPrimeSegment 435814445 435945517).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 435814445 ≤ 435879981)
    (by decide : 435879981 ≤ 435945517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 435814445 435945517).card = 450 := join_1_0

end S207C13
end Sude.GeneratedTwinScan
