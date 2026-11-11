import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21858)) 477757485 477790253 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 477757485 477790253).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21858 477757485 477790253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21859)) 477790253 477823021 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 477790253 477823021).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21859 477790253 477823021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21859)) 477823021 477855789 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 477823021 477855789).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21859 477823021 477855789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21860)) 477855789 477888557 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 477855789 477888557).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21860 477855789 477888557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 477757485 477823021).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 477757485 ≤ 477790253)
    (by decide : 477790253 ≤ 477823021) block0 block1

theorem join_0_1 : (twinPrimeSegment 477823021 477888557).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 477823021 ≤ 477855789)
    (by decide : 477855789 ≤ 477888557) block2 block3

theorem join_1_0 : (twinPrimeSegment 477757485 477888557).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 477757485 ≤ 477823021)
    (by decide : 477823021 ≤ 477888557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 477757485 477888557).card = 438 := join_1_0

end S227C13
end Sude.GeneratedTwinScan
