import Shared.ComplexityBridge.TM2GeneralTM1Costs
import Shared.ComplexityBridge.TM1GeneralTM0Costs

/-! Compose the quantitative TM2-to-TM1 and TM1-to-TM0 simulations.
The source and target alphabets here may be infinite. -/
namespace Shared.ComplexityBridge.TM2GeneralTM0Costs
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2GeneralTM1Costs
open Shared.ComplexityBridge.TM1GeneralTM0Costs

variable {K Λ σ : Type} {Γ : K → Type} [Fintype Λ]

theorem supports_univ_stmt (q : TM2.Stmt Γ Λ σ) : TM2.SupportsStmt Finset.univ q := by
  induction q with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih => exact ih
  | branch f q r ihq ihr => exact ⟨ihq,ihr⟩
  | goto f => intro v; exact Finset.mem_univ _
  | halt => trivial

noncomputable def labels (tm : FinTM2) : Finset tm.Λ := by
  classical
  letI := tm.ΛFin
  exact Finset.univ

theorem source_support (tm : FinTM2) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM2.Supports tm.m (labels tm) := by
  classical
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  letI := tm.ΛFin
  constructor
  · simp [labels]
  · intro q hq
    exact supports_univ_stmt (tm.m q)

noncomputable def support1 (tm : FinTM2) : Finset (TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  exact TM2to1.trSupp tm.m (labels tm)

theorem support1_correct (tm : FinTM2) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM1.Supports (TM2to1.tr tm.m) (support1 tm) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  exact TM2to1.tr_supports tm.m (source_support tm)

/-- The translated post-Turing control has finite reachable support, even
if the source's internal tape alphabets are not yet proved finite. -/
noncomputable def support0 (tm : FinTM2) : Finset (TM1to0.Λ' (TM2to1.tr tm.m)) := by
  letI := tm.σFin
  exact TM1to0.trStmts (TM2to1.tr tm.m) (support1 tm)

theorem support0_correct (tm : FinTM2) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM0.Supports (TM1to0.tr (TM2to1.tr tm.m)) (support0 tm : Set _) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  letI := tm.σFin
  exact TM1to0.tr_supports (TM2to1.tr tm.m) (support1_correct tm)

noncomputable def postLimit (tm : FinTM2) : Nat := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  exact statementLimit (TM2to1.tr tm.m) (support1 tm)

noncomputable def timePolynomial (tm : FinTM2) (p : Polynomial Nat) : Polynomial Nat :=
  simulationPolynomial tm p * Polynomial.C (postLimit tm)

/-- Every polynomially bounded successful TM2 input run has a matching TM0
run from the actual translated initial tape, with a polynomial number of
post-Turing transitions. -/
theorem run_from_input_polynomial (tm : FinTM2) (p : Polynomial Nat)
    (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg)
    (hrun : runSteps tm.step n (Turing.initList tm bits) = some last)
    (htime : n ≤ p.eval bits.length) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ d z, n ≤ d ∧ d ≤ (timePolynomial tm p).eval bits.length ∧
      ∃ mid, TM2to1.TrCfg last mid ∧ z = TM1to0.trCfg (TM2to1.tr tm.m) mid ∧
        runSteps (TM0.step (TM1to0.tr (TM2to1.tr tm.m))) d
          (TM1to0.trCfg (TM2to1.tr tm.m) (translatedInitial tm bits)) = some z := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨k,mid,hkpos,hk,hr,hrel⟩ := TM2GeneralTM1Costs.run_from_input_polynomial tm p bits n last hrun htime
  have hsup := support1_correct tm
  have hmem : (translatedInitial tm bits).l ∈ (support1 tm).insertNone := by
    change some default ∈ (support1 tm).insertNone
    exact Finset.some_mem_insertNone.2 hsup.1
  obtain ⟨d,hdpos,hd,he⟩ := TM1GeneralTM0Costs.run_bounded (TM2to1.tr tm.m) (support1 tm)
    hsup k (translatedInitial tm bits) mid hmem hr
  refine ⟨d,TM1to0.trCfg (TM2to1.tr tm.m) mid,by omega,?_,mid,hrel,rfl,he⟩
  change d ≤ (simulationPolynomial tm p * Polynomial.C (postLimit tm)).eval bits.length
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  have hb := Nat.mul_le_mul_right (postLimit tm) hk
  change d ≤ k * postLimit tm at hd
  exact le_trans hd hb

/-- The composed initial configuration is mathlib's ordinary TM0 input
configuration for the translated stack tape. -/
theorem initial_is_tm0_init (tm : FinTM2) (bits : List (tm.Γ tm.k₀)) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM1to0.trCfg (TM2to1.tr tm.m) (translatedInitial tm bits) =
      TM0.init (TM2to1.trInit tm.k₀ bits) := by
  rfl

/-- Halting is preserved at the final boundary, without adding an absorbing
continuation or silently changing the output tape. -/
theorem translated_halt (tm : FinTM2) (last : tm.Cfg)
    (mid : TM1.Cfg (TM2to1.Γ' tm.K tm.Γ) (TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ)
    (hrel : TM2to1.TrCfg last mid) (hhalt : last.l = none) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM0.step (TM1to0.tr (TM2to1.tr tm.m)) (TM1to0.trCfg (TM2to1.tr tm.m) mid) = none := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  cases hrel with
  | @mk l v S L hL =>
    cases l with
    | none => rfl
    | some q => simp at hhalt

/-- The composed polynomial simulation reaches a genuine post-Turing halt
whenever the source run finishes halted. -/
theorem halt_from_input_polynomial (tm : FinTM2) (p : Polynomial Nat)
    (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg)
    (hrun : runSteps tm.step n (Turing.initList tm bits) = some last)
    (htime : n ≤ p.eval bits.length) (hhalt : last.l = none) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ d z, n ≤ d ∧ d ≤ (timePolynomial tm p).eval bits.length ∧
      runSteps (TM0.step (TM1to0.tr (TM2to1.tr tm.m))) d
        (TM0.init (TM2to1.trInit tm.k₀ bits)) = some z ∧
      TM0.step (TM1to0.tr (TM2to1.tr tm.m)) z = none ∧
      ∃ mid, TM2to1.TrCfg last mid ∧ z = TM1to0.trCfg (TM2to1.tr tm.m) mid := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨d,z,hlo,hhi,mid,hrel,hz,hr⟩ := run_from_input_polynomial tm p bits n last hrun htime
  refine ⟨d,z,hlo,hhi,?_,?_,mid,hrel,hz⟩
  · rw [← initial_is_tm0_init tm bits]
    exact hr
  · rw [hz]
    exact translated_halt tm last mid hrel hhalt

end Shared.ComplexityBridge.TM2GeneralTM0Costs
