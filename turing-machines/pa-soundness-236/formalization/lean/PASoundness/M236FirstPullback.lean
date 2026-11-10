import PASoundness.M236FirstDecode
/-! Pull back the first exact selected-table root configuration through its
unique quotient preimage, to continue the same raw execution. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.BlankFirst
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- The selected grammar root has exactly one raw-state preimage. -/
theorem root_preimage : ∀ q : Fin 237, mapState q = 78 → q = 79 := by decide

/-- The first decoded root tape belongs to the same raw blank-start run. -/
theorem first_zero_control_raw :
    ∃ (time : Nat) (endHead : Int), 0 < time ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ []),
          [false, false, true] ++ (List.replicate 3818 false ++ true :: false ::
            (bank (UnaryNine.values zeros ++ reserve) ++ [false]))⟩⟩
        ((machineWordSystem raw rawLabels).run (89821408 + time)) ∧
      (machineWordSystem raw rawLabels).prefixWord (89821408 + time) = [] := by
  obtain ⟨time, endHead, ht, hr, he⟩ := first_zero_control_from_blank
  have hmap : mapConfig ((machineWordSystem raw rawLabels).run (89821408 + time)) =
      (machineWordSystem machine machineLabels).run (89821408 + time) := by
    rw [machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  rw [← hmap] at hr
  have hstate := root_preimage _ hr.1.symm
  refine ⟨time, endHead, ht, ?_, ?_⟩
  · exact ⟨hstate.symm, hr.2.1, hr.2.2⟩
  · rw [prefix_eq]; exact he
end PASoundness.M236.BlankFirst
