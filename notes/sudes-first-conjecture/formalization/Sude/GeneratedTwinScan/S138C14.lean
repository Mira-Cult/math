import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17066)) 291242029 291274797 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 291242029 291274797).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17066 291242029 291274797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17067)) 291274797 291307565 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291274797 291307565).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17067 291274797 291307565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17068)) 291307565 291340333 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291307565 291340333).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17068 291307565 291340333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17069)) 291340333 291373101 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291340333 291373101).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17069 291340333 291373101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 291242029 291307565).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 291242029 ≤ 291274797)
    (by decide : 291274797 ≤ 291307565) block0 block1

theorem join_0_1 : (twinPrimeSegment 291307565 291373101).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 291307565 ≤ 291340333)
    (by decide : 291340333 ≤ 291373101) block2 block3

theorem join_1_0 : (twinPrimeSegment 291242029 291373101).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 291242029 ≤ 291307565)
    (by decide : 291307565 ≤ 291373101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 291242029 291373101).card = 457 := join_1_0

end S138C14
end Sude.GeneratedTwinScan
