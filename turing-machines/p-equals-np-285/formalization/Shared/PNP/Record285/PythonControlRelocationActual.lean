import Shared.PNP.Record285.PythonControlRelocationRegion
import Shared.PNP.Record285.PythonControlSettle

/-! One actual labelled reference step is matched by the candidate decoder
at its relocated address, even when loop dedents must first be normalized.
The theorem is local: it does not assert that every reachable step remains in
the decoder region. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationActual
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationStep
open Shared.PNP.Record285.PythonControlRelocationRegion
open Shared.PNP.Record285.PythonControlSettle

theorem decoder_step (pc : Nat) (s : Store) (inner : List Loop)
    (hlo : 47 ≤ pc) (hhi : pc ≤ 65)
    (hheads : ∀ l ∈ inner, 47 ≤ l.head ∧ l.head ≤ 65)
    (hinside : (settle pc (inner++referenceBase)).1 < 65) :
    let r := step code (.live ⟨pc,s,inner++referenceBase⟩)
    let c := step code (.live ⟨pc+47,s,inner.map shiftLoop++candidateBase⟩)
    r.2=c.2 ∧ Matched r.1 c.1 := by
  obtain ⟨target,remaining,htlo,hthi,href,hcand⟩ := settle_shared pc inner hlo hhi hheads
  have htinside : target < 65 := by simpa only [href,Prod.fst] using hinside
  let i := target-47
  have hindex : i < 18 := by dsimp [i]; omega
  have ht : 47+i=target := by dsimp [i]; omega
  obtain ⟨line,hrow,hrowc,hallowed,hedges⟩ := decoder_row i hindex
  rw [ht] at hrow hrowc hedges
  have hrefFixed := settle_idempotent pc (inner++referenceBase)
  rw [href] at hrefFixed
  simp only at hrefFixed
  have hcandFixed := settle_idempotent (pc+47) (inner.map shiftLoop++candidateBase)
  rw [hcand] at hcandFixed
  simp only at hcandFixed
  rw [step_settled pc s (inner++referenceBase) target (remaining++referenceBase) href,
      step_settled (pc+47) s (inner.map shiftLoop++candidateBase) (target+47)
        (remaining.map shiftLoop++candidateBase) hcand]
  exact matched_step target s remaining line hrefFixed hcandFixed hrow hrowc hallowed hedges

end Shared.PNP.Record285.PythonControlRelocationActual
