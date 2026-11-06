import Shared.Codes.TM2CheckedCandidate
import Shared.ComplexityBridge.ParserComputability
import Shared.Beeping.Controller

/-! Executable SAT comparisons using the shared numeric TM2 candidate
universe. The controller theorem is abstract. SAT membership/completeness,
quantitative simulations and finite-table refinement remain
open and are not assumed as axioms. -/
namespace Shared.PNP.TM2Candidate
open Shared.Codes.TM2Candidate

/-- A total comparison with the independently computed all-bitstrings SAT
reference. This is an intermediate candidate family: the polynomial model
bridge is not yet discharged. -/
def comparison {α : Type} (decoded : Option α) (eval : α → Option Bool) (target : Bool) : Bool :=
  match decoded with
  | none => false
  | some c => match eval c with
    | none => false
    | some b => b == target

def compareSAT (e n : Nat) : Bool :=
  comparison (decode e) (fun c => Shared.Codes.TM2CheckedCandidate.evaluate c (Shared.Codes.Inputs.inputAt n))
    (Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt n))

theorem compareSAT_computable : Computable₂ compareSAT := by
  let P := Candidate × Nat
  have hx : Computable (fun p : P => Shared.Codes.Inputs.inputAt p.2) :=
    Shared.Codes.Inputs.computable.comp Computable.snd
  have he : Computable (fun p : P => Shared.Codes.TM2CheckedCandidate.evaluate p.1 (Shared.Codes.Inputs.inputAt p.2)) :=
    Shared.Codes.TM2CheckedCandidate.evaluate_computable.comp Computable.fst hx
  have hs : Computable (fun p : P => Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt p.2)) :=
    Shared.ComplexityBridge.ParserComputability.sat_computable.comp hx
  have hb : Computable₂ (fun (p : P) (b : Bool) =>
      b == Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt p.2)) :=
    (Primrec.beq.to_comp.comp Computable.snd (hs.comp Computable.fst)).to₂
  have hc : Computable (fun p : P => match Shared.Codes.TM2CheckedCandidate.evaluate p.1 (Shared.Codes.Inputs.inputAt p.2) with
      | none => false
      | some b => b == Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt p.2)) := by
    refine (Computable.option_casesOn he (Computable.const false) hb).of_eq ?_
    intro p
    cases Shared.Codes.TM2CheckedCandidate.evaluate p.1 (Shared.Codes.Inputs.inputAt p.2) <;> rfl
  have h := Computable.option_casesOn (decode_primrec.to_comp.comp Computable.fst) (Computable.const false)
    (hc.comp (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))).to₂
  apply h.of_eq
  rintro ⟨e,n⟩
  unfold compareSAT comparison
  cases decode e <;> rfl

theorem comparison_spec {α : Type} (decoded : Option α) (eval : α → Option Bool) (target : Bool) :
    comparison decoded eval target = true ↔ ∃ c, decoded = some c ∧ eval c = some target := by
  cases decoded with
  | none => simp [comparison]
  | some c =>
    cases h : eval c with
    | none => simp [comparison, h]
    | some b => simp [comparison, h]

theorem compareSAT_iff (e n : Nat) : compareSAT e n = true ↔ ∃ c,
    decode e = some c ∧ Shared.Codes.TM2CheckedCandidate.evaluate c (Shared.Codes.Inputs.inputAt n) =
      some (Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt n)) := by
  unfold compareSAT
  exact comparison_spec _ _ _

theorem good_iff (e : Nat) : (∀ n, compareSAT e n = true) ↔ ∃ c,
    decode e = some c ∧ ∀ x, Shared.Codes.TM2CheckedCandidate.evaluate c x = some (Shared.ComplexityBridge.CNF.sat x) := by
  constructor
  · intro h
    obtain ⟨c,hc,_⟩ := (compareSAT_iff e 0).1 (h 0)
    refine ⟨c,hc,?_⟩
    intro x
    obtain ⟨n,hn⟩ := Shared.Codes.Inputs.covers x
    obtain ⟨c',hc',he⟩ := (compareSAT_iff e n).1 (h n)
    have hh : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst c'
    simpa [hn] using he
  · rintro ⟨c,hc,h⟩ n
    exact (compareSAT_iff e n).2 ⟨c,hc,h _⟩

theorem sat_in_P_implies_good (h : Shared.ComplexityBridge.CNF.sat ∈ ComplexityTheory.P) :
    ∃ e, ∀ n, compareSAT e n = true := by
  obtain ⟨c,_,hc⟩ := Shared.Codes.TM2CheckedCandidate.canonicalP_covers Shared.ComplexityBridge.CNF.sat h
  refine ⟨Encodable.encode c, ?_⟩
  exact (good_iff _).2 ⟨c,decode_coverage c,hc⟩

theorem controller_silent_iff :
    (Shared.Beeping.Controller.system compareSAT 0).EventuallySilent ↔
      ∃ c : Candidate, ∀ x, Shared.Codes.TM2CheckedCandidate.evaluate c x = some (Shared.ComplexityBridge.CNF.sat x) := by
  rw [Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good]
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨c,_,hc⟩ := (good_iff e).1 he
    exact ⟨c,hc⟩
  · rintro ⟨c,hc⟩
    exact ⟨Encodable.encode c, (good_iff _).2 ⟨c,decode_coverage c,hc⟩⟩

theorem equality_implies_silence
    (hsat : Shared.ComplexityBridge.CNF.sat ∈ ComplexityTheory.NP)
    (heq : ComplexityTheory.P = ComplexityTheory.NP) :
    (Shared.Beeping.Controller.system compareSAT 0).EventuallySilent := by
  apply (Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good compareSAT).2
  apply sat_in_P_implies_good
  rw [heq]
  exact hsat


end Shared.PNP.TM2Candidate
