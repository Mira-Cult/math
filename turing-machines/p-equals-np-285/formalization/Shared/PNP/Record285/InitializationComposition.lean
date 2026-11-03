import Shared.PNP.Record285.InitializationRounds
import Shared.PNP.Record285.InitializationReturn

/-! Composition of the complete candidate initialization path. The three
finite-certificate premises are explicit until the checked files are imported. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option exponentiation.threshold 8192
namespace Shared.PNP.Record285.InitializationComposition
open Shared.Beeping
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker (silent_compose)
open Shared.PNP.Record285.InitializationChecker
open Shared.PNP.Record285.InitializationRounds
open Shared.PNP.Record285.InitializationReturnCertificate

def candidate : Config 285 := ⟨⟨284,by decide⟩,(-3818:Int),6,false,4^1910*rep4 1910⟩

theorem cfg_zero : cfg 0 = ⟨exit,(-2:Int),rep4 1910+1,false,80⟩ := by decide

theorem total_duration : elapsed 2 1904 = 87481184 := by decide

/-- Once the start, repeated cycles, and final edge certificates have been
checked, the complete blank-start tape and all transition flags follow. -/
theorem source_entry_of_certificates
    (hstart : silent Record285.machine 61396 (cfg 0) = some (cfg 2))
    (hcycles : ∀ n, 2 ≤ n → n < 1906 → checkRound n = true)
    (hend : silent Record285.machine 122388 (cfg 1906) = some candidate) :
    Rel candidate (Record285.machine.system.run 89806142) ∧
      ∀ t, t < 89806142 → ¬ Record285.machine.system.BeepAt t := by
  have hfirst : silent Record285.machine 2133492
      ⟨A,0,0,false,0⟩ = some ⟨exit,(-2:Int),rep4 1910,true,30⟩ := by
    rw [numeric_silent]
    exact BootstrapTraceProof.bootstrap_shape NumericTables.target BootstrapRows.numeric_rows
  have hbase : silent Record285.machine 2141174 ⟨A,0,0,false,0⟩ = some (cfg 0) := by
    rw [cfg_zero]
    exact silent_compose Record285.machine ⟨A,0,0,false,0⟩
      ⟨exit,(-2:Int),rep4 1910,true,30⟩ ⟨exit,(-2:Int),rep4 1910+1,false,80⟩
      2133492 7682 hfirst return_run
  have hmid : silent Record285.machine 87481184 (cfg 2) = some (cfg 1906) := by
    have h := checked_rounds 2 1904 (by intro n hn hl; exact hcycles n hn (by omega))
    rw [total_duration] at h
    exact h
  have hpre := silent_compose Record285.machine ⟨A,0,0,false,0⟩ (cfg 0) (cfg 2)
    2141174 61396 hbase hstart
  have hloop := silent_compose Record285.machine ⟨A,0,0,false,0⟩ (cfg 2) (cfg 1906)
    2202570 87481184 hpre hmid
  have hall := silent_compose Record285.machine ⟨A,0,0,false,0⟩ (cfg 1906) candidate
    89683754 122388 hloop hend
  exact silent_physical Record285.machine (PhysicalNumeric.initial Record285.machine)
    Record285.machine.initial (initial_related Record285.machine rfl) 89806142 candidate hall

end Shared.PNP.Record285.InitializationComposition
