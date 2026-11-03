import Shared.PNP.Record285.InitializationReturnCertificate
import Shared.PNP.Record285.BootstrapTraceProof

/-! Exact blank-start reachability through a subsequent return to state
76. This does not assert source entry or global progress of later phases. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.InitializationReturn
open Shared.Beeping
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker (silent_compose)
open Shared.PNP.Record285.InitializationChecker
open Shared.PNP.Record285.InitializationReturnCertificate

/-- The complete literal physical configuration after the return,
and absence of events on every preceding transition. -/
theorem blank_start_return :
    Rel ⟨exit,(-2:Int),rep4 1910+1,false,80⟩
      (Record285.machine.system.run 2141174) ∧
    ∀ t, t < 2141174 → ¬ Record285.machine.system.BeepAt t := by
  have hfirst : silent Record285.machine 2133492
      ⟨A,0,0,false,0⟩ = some ⟨exit,(-2:Int),rep4 1910,true,30⟩ := by
    rw [numeric_silent]
    exact BootstrapTraceProof.bootstrap_shape NumericTables.target BootstrapRows.numeric_rows
  have htotal := silent_compose Record285.machine ⟨A,0,0,false,0⟩
    ⟨exit,(-2:Int),rep4 1910,true,30⟩ ⟨exit,(-2:Int),rep4 1910+1,false,80⟩
    2133492 7682 hfirst return_run
  exact silent_physical Record285.machine (PhysicalNumeric.initial Record285.machine)
    Record285.machine.initial (initial_related Record285.machine rfl)
    2141174 ⟨exit,(-2:Int),rep4 1910+1,false,80⟩ htotal

theorem related_read (c : PhysicalNumeric.Config 285) (p : Shared.Beeping.Machines.Config 285)
    (h : Rel c p) : p.tape p.head = c.read := h.2.2.1

/-- State 76 reading zero is actually reached from blank. The number is in the
final marked table, not the producer's intermediate completion-table numbering. -/
theorem row_76_zero_reachable :
    (Record285.machine.system.run 2141174).state.val = 76 ∧
      (Record285.machine.system.run 2141174).tape
        (Record285.machine.system.run 2141174).head = false := by
  have h := blank_start_return.1
  have hs : (Record285.machine.system.run 2141174).state = exit := h.1.symm
  have ht := related_read ⟨exit,(-2:Int),rep4 1910+1,false,80⟩
    (Record285.machine.system.run 2141174) h
  constructor
  · rw [hs]; rfl
  · exact ht

end Shared.PNP.Record285.InitializationReturn
