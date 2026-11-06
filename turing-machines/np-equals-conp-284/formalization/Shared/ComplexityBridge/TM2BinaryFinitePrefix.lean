import Shared.ComplexityBridge.TM2BinaryFiniteProgram

/-! Quantitative finite-prefix TM2-to-binary-program simulation. Unlike the
halted-output theorem, this preserves the entire final tape and a live finite
control state for every successful run, including continuing handoffs. The
input is the serialized TM2 initial tape; raw-input preprocessing and a
particular verifier handoff are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BinaryFinitePrefix

open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2GeneralTM1Costs
open Shared.ComplexityBridge.TM2GeneralTM0Costs
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms

/-- Nonhalting form of the quantitative binary post-Turing simulation. -/
theorem post_prefix (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
    {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a)
    (p : Polynomial Nat) (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg)
    (hrun : runSteps tm.step n (Turing.initList tm bits) = some last)
    (htime : n ≤ p.eval bits.length) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ d, n ≤ d ∧ d ≤ (timePolynomial tm alphabet enc dec p).eval bits.length ∧
      ∃ mid, TM2to1.TrCfg last mid ∧
        runSteps (TM0.step (TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m)))) d
          (TM0.init (inputBits tm enc bits)) =
          some (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨k,mid,hklo,hkhi,hk,hrel⟩ := TM2GeneralTM1Costs.run_from_input_polynomial tm p bits n last hrun htime
  have hs := support1_correct tm
  have hmem : (translatedInitial tm bits).l ∈ (support1 tm).insertNone := by
    change some default ∈ (support1 tm).insertNone
    exact Finset.some_mem_insertNone.2 hs.1
  obtain ⟨d,hdlo,hdhi,hd⟩ := TM1BinaryPostCosts.run_bounded enc dec enc0 encdec (TM2to1.tr tm.m)
    (support1 tm) hs k (translatedInitial tm bits) mid hmem hk
  have hd' : runSteps (TM0.step (TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m)))) d
      (TM0.init (inputBits tm enc bits)) =
      some (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)) := by
    rw [← initial_eq_input tm enc dec enc0 bits]
    exact hd
  refine ⟨d,by omega,?_,mid,hrel,hd'⟩
  simp only [TM2BinaryPostCosts.timePolynomial,Polynomial.eval_mul,Polynomial.eval_C]
  have hh := Nat.mul_le_mul_right (binaryPostLimit tm alphabet enc dec) hkhi
  have hbound : d ≤ k * binaryPostLimit tm alphabet enc dec := by
    simpa [binaryPostLimit,Nat.mul_assoc] using hdhi
  exact le_trans hbound hh

/-- A finite indexed program preserves every successful supported post-Turing
prefix and its entire tape, without requiring the final state to halt. -/
theorem finite_post_prefix {Λ : Type} [Inhabited Λ] (M : TM0.Machine Bool Λ)
    (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ)) :
    ∃ program : Program, valid program = true ∧
      (∀ q, TM0FiniteProgram.mainIndex (TM0FiniteReindex.index M S hs q) < program.length) ∧
      ∀ (input : List Bool) (n : Nat) (last : TM0.Cfg Bool Λ),
        runSteps (TM0.step M) n (TM0.init input) = some last →
        ∃ d tape', n ≤ d ∧ d ≤ 2*n ∧
          TM0FiniteProgram.tape tape' = last.Tape ∧
          run program (initial input) d =
            some (.inr (TM0FiniteProgram.mainIndex (TM0FiniteReindex.index M S hs last.q),tape')) := by
  letI : Inhabited (Fin S.card) := ⟨TM0FiniteReindex.zero M S hs⟩
  let P := TM0FiniteReindex.machine M S hs
  refine ⟨TM0FiniteProgram.program P,TM0FiniteProgram.program_valid P,?_,?_⟩
  · intro q
    rw [TM0FiniteProgram.program_length]
    have h := (TM0FiniteReindex.index M S hs q).isLt
    dsimp [TM0FiniteProgram.mainIndex]
    omega
  intro input n last hrun
  have hinit : (TM0.init input : TM0.Cfg Bool Λ).q ∈ S := hs.1
  obtain ⟨hr,_⟩ := TM0FiniteReindex.run_map M S hs n (TM0.init input) last hinit hrun
  rw [TM0FiniteReindex.initial_config] at hr
  change runSteps (TM0.step P) n ⟨TM0FiniteReindex.zero M S hs,Tape.mk₁ input⟩ =
      some (TM0FiniteReindex.config M S hs last) at hr
  have hsrun : runSteps (TM0.step P) n
      ⟨TM0FiniteReindex.zero M S hs,TM0FiniteProgram.tape (initial input).2⟩ =
      some ⟨TM0FiniteReindex.index M S hs last.q,last.Tape⟩ := by
    simpa [P,TM0.init,TM0FiniteReindex.config,TM0FiniteProgram.tape_initial] using hr
  obtain ⟨d,tape',hlo,hhi,ht,hsim⟩ := TM0FiniteProgram.run_simulation P n (TM0FiniteReindex.zero M S hs)
    (TM0FiniteReindex.index M S hs last.q) (initial input).2 last.Tape hsrun
  have hstart : TM0FiniteProgram.mainIndex (TM0FiniteReindex.zero M S hs) = 0 := by
    rfl
  have hcfg : (TM0FiniteProgram.mainIndex (TM0FiniteReindex.zero M S hs),(initial input).2) = initial input := by
    simp [hstart,initial]
  rw [hcfg] at hsim
  exact ⟨d,tape',hlo,hhi,ht,hsim⟩

/-- One finite program simulates every polynomially bounded finite TM2 input
run on its encoded initial tape. It reaches a live control state and retains
the exact represented tape, even when the original run has not halted. -/
theorem finite_tm2_prefix (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
    {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) (p : Polynomial Nat) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ program : Program, valid program = true ∧
      ∀ (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg),
        runSteps tm.step n (Turing.initList tm bits) = some last →
        n ≤ p.eval bits.length →
        ∃ d q tape' mid, n ≤ d ∧
          d ≤ (2*timePolynomial tm alphabet enc dec p).eval bits.length ∧
          TM2to1.TrCfg last mid ∧
          TM0FiniteProgram.tape tape' =
            (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)).Tape ∧
          run program (initial (inputBits tm enc bits)) d = some (.inr (q,tape')) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
  let S := support0 tm alphabet enc dec
  have hs : TM0.Supports M (S : Set _) := support0_correct tm alphabet enc dec
  obtain ⟨program,hvalid,_,hprogram⟩ := finite_post_prefix M S hs
  refine ⟨program,hvalid,?_⟩
  intro bits n last hrun htime
  obtain ⟨k,hklo,hkhi,mid,hrel,hr⟩ := post_prefix tm alphabet enc dec enc0 encdec p bits n last hrun htime
  obtain ⟨d,tape',hdlo,hdhi,ht,he⟩ := hprogram (inputBits tm enc bits) k _ hr
  refine ⟨d,_,tape',mid,by omega,?_,hrel,ht,he⟩
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

/-- Strengthened finite-prefix simulation: the reached finite control is a
fixed function of the translated post-Turing control, independent of its tape.
This makes a continuing handoff state available for later linking. -/
theorem finite_tm2_prefix_control (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
    {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) (p : Polynomial Nat) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ (program : Program)
      (control : TM1to0.Λ' (TM1to1.tr enc dec (TM2to1.tr tm.m)) → Nat),
      valid program = true ∧ (∀ q, control q < program.length) ∧
      ∀ (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg),
        runSteps tm.step n (Turing.initList tm bits) = some last →
        n ≤ p.eval bits.length →
        ∃ d tape' mid, n ≤ d ∧
          d ≤ (2*timePolynomial tm alphabet enc dec p).eval bits.length ∧
          TM2to1.TrCfg last mid ∧
          TM0FiniteProgram.tape tape' =
            (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)).Tape ∧
          run program (initial (inputBits tm enc bits)) d =
            some (.inr (control (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m))
              (TM1to1.trCfg enc enc0 mid)).q,tape')) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
  let S := support0 tm alphabet enc dec
  have hs : TM0.Supports M (S : Set _) := support0_correct tm alphabet enc dec
  obtain ⟨program,hvalid,hcontrol,hprogram⟩ := finite_post_prefix M S hs
  refine ⟨program,(fun q => TM0FiniteProgram.mainIndex (TM0FiniteReindex.index M S hs q)),hvalid,hcontrol,?_⟩
  intro bits n last hrun htime
  obtain ⟨k,hklo,hkhi,mid,hrel,hr⟩ := post_prefix tm alphabet enc dec enc0 encdec p bits n last hrun htime
  obtain ⟨d,tape',hdlo,hdhi,ht,he⟩ := hprogram (inputBits tm enc bits) k _ hr
  refine ⟨d,tape',mid,by omega,?_,hrel,ht,he⟩
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

end Shared.ComplexityBridge.TM2BinaryFinitePrefix
