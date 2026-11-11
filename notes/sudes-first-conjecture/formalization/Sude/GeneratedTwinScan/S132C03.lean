import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16650)) 277217325 277250093 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 277217325 277250093).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16650 277217325 277250093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16651)) 277250093 277282861 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 277250093 277282861).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16651 277250093 277282861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16652)) 277282861 277315629 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277282861 277315629).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16652 277282861 277315629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16653)) 277315629 277348397 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277315629 277348397).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16653 277315629 277348397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 277217325 277282861).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 277217325 ≤ 277250093)
    (by decide : 277250093 ≤ 277282861) block0 block1

theorem join_0_1 : (twinPrimeSegment 277282861 277348397).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 277282861 ≤ 277315629)
    (by decide : 277315629 ≤ 277348397) block2 block3

theorem join_1_0 : (twinPrimeSegment 277217325 277348397).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 277217325 ≤ 277282861)
    (by decide : 277282861 ≤ 277348397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 277217325 277348397).card = 437 := join_1_0

end S132C03
end Sude.GeneratedTwinScan
