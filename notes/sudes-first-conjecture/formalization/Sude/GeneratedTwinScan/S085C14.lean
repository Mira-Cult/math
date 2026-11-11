import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13421)) 180092973 180125741 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 180092973 180125741).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13421 180092973 180125741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13422)) 180125741 180158509 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 180125741 180158509).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13422 180125741 180158509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13423)) 180158509 180191277 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180158509 180191277).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13423 180158509 180191277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13424)) 180191277 180224045 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180191277 180224045).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13424 180191277 180224045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 180092973 180158509).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 180092973 ≤ 180125741)
    (by decide : 180125741 ≤ 180158509) block0 block1

theorem join_0_1 : (twinPrimeSegment 180158509 180224045).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 180158509 ≤ 180191277)
    (by decide : 180191277 ≤ 180224045) block2 block3

theorem join_1_0 : (twinPrimeSegment 180092973 180224045).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 180092973 ≤ 180158509)
    (by decide : 180158509 ≤ 180224045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 180092973 180224045).card = 470 := join_1_0

end S085C14
end Sude.GeneratedTwinScan
