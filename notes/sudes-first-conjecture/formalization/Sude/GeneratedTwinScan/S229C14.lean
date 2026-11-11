import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21957)) 482082861 482115629 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 482082861 482115629).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21957 482082861 482115629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21957)) 482115629 482148397 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 482115629 482148397).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21957 482115629 482148397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21958)) 482148397 482181165 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 482148397 482181165).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21958 482148397 482181165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21959)) 482181165 482213933 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 482181165 482213933).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21959 482181165 482213933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 482082861 482148397).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 482082861 ≤ 482115629)
    (by decide : 482115629 ≤ 482148397) block0 block1

theorem join_0_1 : (twinPrimeSegment 482148397 482213933).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 482148397 ≤ 482181165)
    (by decide : 482181165 ≤ 482213933) block2 block3

theorem join_1_0 : (twinPrimeSegment 482082861 482213933).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 482082861 ≤ 482148397)
    (by decide : 482148397 ≤ 482213933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 482082861 482213933).card = 457 := join_1_0

end S229C14
end Sude.GeneratedTwinScan
