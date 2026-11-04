import Shared.PNP.Record285.LiteralEndpoint
import Shared.PNP.Record285.LiteralQuotient

/-! Reader-facing statements for the two frozen tables. The 285-state table
marks one transition row; the 286-state companion beeps on exit from state 1.
The underlying complexity classes are the upstream canonical definitions. -/
namespace Shared.PNP.Record285.PublicEndpoint
open Shared.Beeping
open Shared.Beeping.Machines

/-- The marked 285-state table beeps finitely often exactly when P = NP. -/
theorem marked_finite_iff_P_eq_NP :
    Record285.machine.system.FiniteEventTimes ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  DirectEndpoint.literal_finiteEvents_iff_P_eq_NP

/-- The companion visits its designated state finitely often exactly when
P = NP. A state visit is counted at the transition leaving that state. -/
theorem companion_finite_visits_iff_P_eq_NP :
    (∃ times : List Nat, ∀ t,
      (Companion.machine.system.run t).state = Companion.beepState → t ∈ times) ↔
      ComplexityTheory.P = ComplexityTheory.NP := by
  have h : (∃ times : List Nat, ∀ t,
      (Companion.machine.system.run t).state = Companion.beepState → t ∈ times) ↔
      (Companion.machine.exiting Companion.beepState).system.FiniteEventTimes := by
    constructor
    · rintro ⟨times,htimes⟩
      refine ⟨times,?_⟩
      intro t ht
      exact htimes t ((Machine.exiting_beep_iff Companion.machine Companion.beepState t).1 ht)
    · rintro ⟨times,htimes⟩
      refine ⟨times,?_⟩
      intro t ht
      exact htimes t ((Machine.exiting_beep_iff Companion.machine Companion.beepState t).2 ht)
  exact h.trans ((Companion.machine.exiting Companion.beepState).system.eventuallySilent_iff_finiteEventTimes.symm.trans
    (LiteralQuotient.silence_iff.symm.trans DirectEndpoint.literal_silent_iff_P_eq_NP))

end Shared.PNP.Record285.PublicEndpoint

#check Shared.PNP.Record285.literal
#check Shared.PNP.Record285.Companion.literal
#print ComplexityTheory.P
#print ComplexityTheory.NP
#check Shared.PNP.Record285.LiteralEndpoint.selected_literal_endpoint
#check Shared.PNP.Record285.PublicEndpoint.marked_finite_iff_P_eq_NP
#check Shared.PNP.Record285.PublicEndpoint.companion_finite_visits_iff_P_eq_NP
#print axioms Shared.PNP.Record285.PublicEndpoint.marked_finite_iff_P_eq_NP
#print axioms Shared.PNP.Record285.PublicEndpoint.companion_finite_visits_iff_P_eq_NP
