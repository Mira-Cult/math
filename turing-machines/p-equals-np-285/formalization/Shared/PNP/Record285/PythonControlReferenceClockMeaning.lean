import Shared.PNP.Record285.PythonControlReferenceClock

/-! Choice-bit handoff between the typed reference clock and the common
source virtual transition. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceClockMeaning
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControlActionMeaning (before)
open Shared.PNP.Record285.PythonControlReferenceClock

def sourceState (s : Store) : SimState := ⟨s "left",s "right",s "state",s "choices"⟩

theorem prepared_fields (s : Store) :
    (prepared s) "steps" = s "steps"-1 ∧
    (prepared s) "digit" = s "radix"+s "remaining" ∧
    (prepared s) "choices" = s "choices"/2 ∧
    (prepared s) "program" = s "program" ∧
    (prepared s) "radix" = s "radix" ∧ (prepared s) "remaining" = s "remaining" ∧
    (prepared s) "expected" = s "expected" ∧ (prepared s) "branches" = s "branches" := by
  simp [prepared,put]

theorem prepared_names (s : Store) :
    (prepared s) "n" = s "n" ∧ (prepared s) "exponent" = s "exponent" := by
  simp [prepared,put]

theorem choice_step (s : Store) :
    simStep (s "radix"+s "remaining") (sourceState s) =
      (simStep ((prepared s) "digit") (before (prepared s))).map
        (fun next => {next with choices := s "choices"/2}) := by
  simp [simStep,sourceState,before,prepared,put] <;> split <;> simp_all <;>
    split <;> simp_all

end Shared.PNP.Record285.PythonControlReferenceClockMeaning
