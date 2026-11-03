import Shared.Beeping.ComparisonTM2

/-! Qualitative translation of the comparison evaluators to mathlib's
single-tape post-Turing model. The tape alphabet is finite but is not binary.
This does not charge an encoding or establish event preservation. -/
namespace Shared.Beeping.ComparisonSingleTape

open Turing
open Turing.PartrecToTM2
open Shared.Beeping.ComparisonTM2

abbrev Stacks := K'
abbrev Symbol := Γ'
abbrev Labels := Λ'
abbrev Store := Option Symbol
abbrev Alphabet := TM2to1.Γ' Stacks (fun _ => Symbol)
abbrev Labels1 := TM2to1.Λ' Stacks (fun _ => Symbol) Labels Store

instance : Fintype Stacks := Fintype.ofList [.main, .rev, .aux, .stack] (by
  intro k; cases k <;> simp)

instance : Fintype Alphabet := TM2to1.Γ'.fintype

def program1 : Labels1 → TM1.Stmt Alphabet Labels1 Store :=
  TM2to1.tr (K := Stacks) (Γ := fun _ => Symbol) tr

def initial1 (c : ToPartrec.Code) (input : List Nat) : TM1.Cfg Alphabet Labels1 Store :=
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  TM1.init (TM2to1.trInit K'.main (trList input))

def program0 (c : ToPartrec.Code) :=
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  TM1to0.tr program1

def initial0 (c : ToPartrec.Code) (input : List Nat) :=
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  TM1to0.trCfg program1 (initial1 c input)

/-- Finite support includes every intermediate program statement and every
finite internal-store value. -/
noncomputable def support0 (c : ToPartrec.Code) :=
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  TM1to0.trStmts program1 (TM2to1.trSupp tr (codeSupp c Cont'.halt))

theorem support0_correct (c : ToPartrec.Code) :
    letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
    TM0.Supports (program0 c) (support0 c : Set (TM1to0.Λ' program1)) := by
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  exact TM1to0.tr_supports program1 (TM2to1.tr_supports tr (tr_supports c Cont'.halt))

/-- The canonical single-tape input contains the translated representation of
the two numerical inputs, with the bottom marker supplied by `trInit`. -/
theorem initial_related (c : ToPartrec.Code) (input : List Nat) :
    TM2to1.TrCfg (init c input) (initial1 c input) := by
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  have h := TM2to1.trCfg_init (Γ := fun _ : Stacks => Symbol) (Λ := Labels) (σ := Store) K'.main (trList input)
  have heq : (TM2.init K'.main (trList input) : TM2.Cfg (fun _ : Stacks => Symbol) Labels Store) =
      init c input := by
    change TM2.Cfg.mk (some (trNormal c Cont'.halt)) none
      (Function.update (fun _ : Stacks => ([] : List Symbol)) K'.main (trList input)) = _
    congr 1
    funext k
    cases k <;> simp [Function.update, init, K'.elim]
  rw [heq] at h
  exact h

/-- A terminating comparison becomes a terminating TM0 computation, and its
final tape encodes exactly the cleaned TM2 result configuration. -/
def Implements (R : Nat → Nat → Bool) : Prop :=
    ∃ c : ToPartrec.Code,
      letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
      TM0.Supports (program0 c) (support0 c : Set (TM1to0.Λ' program1)) ∧
      ∀ e n,
      ∃ final1 : TM1.Cfg Alphabet Labels1 Store,
        TM2to1.TrCfg (halt [result R e n]) final1 ∧
        StateTransition.Reaches (TM0.step (program0 c)) (initial0 c [e,n])
          (TM1to0.trCfg program1 final1) ∧
        TM0.step (program0 c) (TM1to0.trCfg program1 final1) = none

theorem comparison_has_singleTape (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    Implements R := by
  obtain ⟨c,hc⟩ := comparison_has_terminating_tm2 R hR
  refine ⟨c, ?_⟩
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  refine ⟨support0_correct c, ?_⟩
  intro e n
  have htm2 := StateTransition.mem_eval.mpr (hc e n)
  obtain ⟨final1,hrel,heval⟩ := StateTransition.tr_eval (TM2to1.tr_respects tr)
    (initial_related c [e,n]) htm2
  obtain ⟨final0,hfinal,heval0⟩ := StateTransition.tr_eval (TM1to0.tr_respects program1)
    (rfl : TM1to0.trCfg program1 (initial1 c [e,n]) = initial0 c [e,n]) heval
  subst final0
  exact ⟨final1,hrel,(StateTransition.mem_eval.mp heval0).1,(StateTransition.mem_eval.mp heval0).2⟩

theorem pnp_has_singleTape : Implements Shared.PNP.TM2Candidate.compareSAT :=
  comparison_has_singleTape _ Shared.PNP.TM2Candidate.compareSAT_computable

theorem npconp_has_singleTape : Implements Shared.NPCONP.TM2Verifier.compare :=
  comparison_has_singleTape _ Shared.NPCONP.TM2Verifier.compare_computable

end Shared.Beeping.ComparisonSingleTape
