import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21293)) 453378093 453410861 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 453378093 453410861).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21293 453378093 453410861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21294)) 453410861 453443629 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453410861 453443629).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21294 453410861 453443629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21294)) 453443629 453476397 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453443629 453476397).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21294 453443629 453476397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21295)) 453476397 453509165 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 453476397 453509165).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21295 453476397 453509165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 453378093 453443629).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 453378093 ≤ 453410861)
    (by decide : 453410861 ≤ 453443629) block0 block1

theorem join_0_1 : (twinPrimeSegment 453443629 453509165).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 453443629 ≤ 453476397)
    (by decide : 453476397 ≤ 453509165) block2 block3

theorem join_1_0 : (twinPrimeSegment 453378093 453509165).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 453378093 ≤ 453443629)
    (by decide : 453443629 ≤ 453509165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 453378093 453509165).card = 417 := join_1_0

end S216C03
end Sude.GeneratedTwinScan
