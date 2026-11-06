import Shared.Beeping.TM0Totalize

/-! The two finite comparison evaluators have silent totalized single-tape
executions retaining the correct output tape. This is not a binary-tape or
controller compiler; the translated input is still preloaded. -/
namespace Shared.Beeping.ComparisonTotalized
open Turing Turing.PartrecToTM2
open Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.TM0Totalize
open Shared.Beeping.ComparisonTM2

def Implements (R : Nat → Nat → Bool) : Prop :=
  ∃ c : ToPartrec.Code,
    letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
    ∀ e n, ∃ (final1 : TM1.Cfg Alphabet Labels1 Store) (d : Nat),
      TM2to1.TrCfg (halt [result R e n]) final1 ∧
      (∀ k, (system (program0 c) (initial0 c [e,n])).run (d + 1 + k) =
        stopped (TM1to0.trCfg program1 final1).Tape) ∧
      (system (program0 c) (initial0 c [e,n])).EventuallySilent

theorem of_singleTape (R : Nat → Nat → Bool)
    (h : Shared.Beeping.ComparisonSingleTape.Implements R) : Implements R := by
  obtain ⟨c,hc⟩ := h
  refine ⟨c, ?_⟩
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  intro e n
  obtain ⟨final1,hrel,hreach,hhalt⟩ := hc.2 e n
  obtain ⟨d,hd⟩ := reaches_runSteps hreach
  refine ⟨final1,d,hrel,terminal_run (program0 c) (initial0 c [e,n]) _ d hd hhalt, ?_⟩
  exact eventuallySilent (program0 c) (initial0 c [e,n])

theorem pnp : Implements Shared.PNP.TM2Candidate.compareSAT := of_singleTape _ pnp_has_singleTape

theorem npconp : Implements Shared.NPCONP.TM2Verifier.compare := of_singleTape _ npconp_has_singleTape

end Shared.Beeping.ComparisonTotalized
