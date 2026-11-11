import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13820)) 190971949 191004717 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190971949 191004717).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13820 190971949 191004717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13821)) 191004717 191037485 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191004717 191037485).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13821 191004717 191037485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13822)) 191037485 191070253 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191037485 191070253).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13822 191037485 191070253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13824)) 191070253 191103021 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191070253 191103021).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13824 191070253 191103021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190971949 191037485).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 190971949 ≤ 191004717)
    (by decide : 191004717 ≤ 191037485) block0 block1

theorem join_0_1 : (twinPrimeSegment 191037485 191103021).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 191037485 ≤ 191070253)
    (by decide : 191070253 ≤ 191103021) block2 block3

theorem join_1_0 : (twinPrimeSegment 190971949 191103021).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 190971949 ≤ 191037485)
    (by decide : 191037485 ≤ 191103021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190971949 191103021).card = 470 := join_1_0

end S091C01
end Sude.GeneratedTwinScan
