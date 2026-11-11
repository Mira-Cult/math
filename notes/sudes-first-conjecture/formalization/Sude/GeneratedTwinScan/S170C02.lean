import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18889)) 356778029 356810797 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 356778029 356810797).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18889 356778029 356810797
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18890)) 356810797 356843565 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 356810797 356843565).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18890 356810797 356843565
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18891)) 356843565 356876333 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 356843565 356876333).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18891 356843565 356876333
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18892)) 356876333 356909101 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 356876333 356909101).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18892 356876333 356909101
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 356778029 356843565).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 356778029 ≤ 356810797)
    (by decide : 356810797 ≤ 356843565) block0 block1

theorem join_0_1 : (twinPrimeSegment 356843565 356909101).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 356843565 ≤ 356876333)
    (by decide : 356876333 ≤ 356909101) block2 block3

theorem join_1_0 : (twinPrimeSegment 356778029 356909101).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 356778029 ≤ 356843565)
    (by decide : 356843565 ≤ 356909101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 356778029 356909101).card = 452 := join_1_0

end S170C02
end Sude.GeneratedTwinScan
