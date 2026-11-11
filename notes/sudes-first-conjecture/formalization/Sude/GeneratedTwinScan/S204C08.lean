import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20709)) 428867629 428900397 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 428867629 428900397).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20709 428867629 428900397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20710)) 428900397 428933165 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 428900397 428933165).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20710 428900397 428933165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20711)) 428933165 428965933 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 428933165 428965933).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20711 428933165 428965933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20712)) 428965933 428998701 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 428965933 428998701).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20712 428965933 428998701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 428867629 428933165).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 428867629 ≤ 428900397)
    (by decide : 428900397 ≤ 428933165) block0 block1

theorem join_0_1 : (twinPrimeSegment 428933165 428998701).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 428933165 ≤ 428965933)
    (by decide : 428965933 ≤ 428998701) block2 block3

theorem join_1_0 : (twinPrimeSegment 428867629 428998701).card = 408 := by
  simpa using combineTwinPrimeSegments (by decide : 428867629 ≤ 428933165)
    (by decide : 428933165 ≤ 428998701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 428867629 428998701).card = 408 := join_1_0

end S204C08
end Sude.GeneratedTwinScan
