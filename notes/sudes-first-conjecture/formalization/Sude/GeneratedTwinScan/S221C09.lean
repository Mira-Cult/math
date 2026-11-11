import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21556)) 464650285 464683053 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 464650285 464683053).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21556 464650285 464683053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21557)) 464683053 464715821 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464683053 464715821).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21557 464683053 464715821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21558)) 464715821 464748589 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464715821 464748589).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21558 464715821 464748589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21558)) 464748589 464781357 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 464748589 464781357).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21558 464748589 464781357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 464650285 464715821).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 464650285 ≤ 464683053)
    (by decide : 464683053 ≤ 464715821) block0 block1

theorem join_0_1 : (twinPrimeSegment 464715821 464781357).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 464715821 ≤ 464748589)
    (by decide : 464748589 ≤ 464781357) block2 block3

theorem join_1_0 : (twinPrimeSegment 464650285 464781357).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 464650285 ≤ 464715821)
    (by decide : 464715821 ≤ 464781357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 464650285 464781357).card = 446 := join_1_0

end S221C09
end Sude.GeneratedTwinScan
