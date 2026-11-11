import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19774)) 390987821 391020589 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 390987821 391020589).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19774 390987821 391020589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19775)) 391020589 391053357 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 391020589 391053357).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19775 391020589 391053357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19775)) 391053357 391086125 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 391053357 391086125).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19775 391053357 391086125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19776)) 391086125 391118893 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 391086125 391118893).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19776 391086125 391118893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 390987821 391053357).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 390987821 ≤ 391020589)
    (by decide : 391020589 ≤ 391053357) block0 block1

theorem join_0_1 : (twinPrimeSegment 391053357 391118893).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 391053357 ≤ 391086125)
    (by decide : 391086125 ≤ 391118893) block2 block3

theorem join_1_0 : (twinPrimeSegment 390987821 391118893).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 390987821 ≤ 391053357)
    (by decide : 391053357 ≤ 391118893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 390987821 391118893).card = 434 := join_1_0

end S186C07
end Sude.GeneratedTwinScan
