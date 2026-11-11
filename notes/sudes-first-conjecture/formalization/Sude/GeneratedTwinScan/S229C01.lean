import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21918)) 480378925 480411693 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 480378925 480411693).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21918 480378925 480411693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21919)) 480411693 480444461 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 480411693 480444461).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21919 480411693 480444461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21919)) 480444461 480477229 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 480444461 480477229).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21919 480444461 480477229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21920)) 480477229 480509997 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 480477229 480509997).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21920 480477229 480509997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 480378925 480444461).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 480378925 ≤ 480411693)
    (by decide : 480411693 ≤ 480444461) block0 block1

theorem join_0_1 : (twinPrimeSegment 480444461 480509997).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 480444461 ≤ 480477229)
    (by decide : 480477229 ≤ 480509997) block2 block3

theorem join_1_0 : (twinPrimeSegment 480378925 480509997).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 480378925 ≤ 480444461)
    (by decide : 480444461 ≤ 480509997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 480378925 480509997).card = 434 := join_1_0

end S229C01
end Sude.GeneratedTwinScan
