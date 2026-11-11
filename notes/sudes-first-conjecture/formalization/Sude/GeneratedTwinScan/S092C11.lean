import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13943)) 194379821 194412589 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 194379821 194412589).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13943 194379821 194412589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13944)) 194412589 194445357 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 194412589 194445357).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13944 194412589 194445357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13945)) 194445357 194478125 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 194445357 194478125).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13945 194445357 194478125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13946)) 194478125 194510893 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 194478125 194510893).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13946 194478125 194510893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 194379821 194445357).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 194379821 ≤ 194412589)
    (by decide : 194412589 ≤ 194445357) block0 block1

theorem join_0_1 : (twinPrimeSegment 194445357 194510893).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 194445357 ≤ 194478125)
    (by decide : 194478125 ≤ 194510893) block2 block3

theorem join_1_0 : (twinPrimeSegment 194379821 194510893).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 194379821 ≤ 194445357)
    (by decide : 194445357 ≤ 194510893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 194379821 194510893).card = 475 := join_1_0

end S092C11
end Sude.GeneratedTwinScan
