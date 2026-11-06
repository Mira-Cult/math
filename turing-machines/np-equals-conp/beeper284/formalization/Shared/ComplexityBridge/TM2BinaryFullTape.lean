import Shared.ComplexityBridge.TM2BinaryFiniteProgram
import Shared.ComplexityBridge.TM0FiniteFullTape

/-! Quantitative finite-table simulation preserving the complete encoded TM2
output tape. Input and output are still in the fixed-width simulation codec. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BinaryFullTape
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms

variable (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
variable {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
variable (dec : List.Vector Bool width → Alphabet tm)
variable (enc0 : enc default = List.Vector.replicate width false)
variable (encdec : ∀ a, dec (enc a) = a)

include encdec

/-- One valid finite binary program simulates all bounded halted runs of a
fixed TM2. At the end of the charged segment, its entire tape equals the
binary encoding of the related TM1 tape, modulo trailing blanks. -/
theorem finite_program_full_tape (clock : Polynomial Nat) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ program : Program, valid program = true ∧
      ∀ (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg),
        runSteps tm.step n (Turing.initList tm bits) = some last →
        n ≤ clock.eval bits.length → last.l = none →
        ∃ d ≤ (2*timePolynomial tm alphabet enc dec clock).eval bits.length,
          ∃ mid q t, TM2to1.TrCfg last mid ∧
            run program (initial (inputBits tm enc bits)) d = some (.inr (q,t)) ∧
            Shared.ComplexityBridge.TM0FiniteProgram.tape t = TM1to1.trTape enc0 mid.Tape ∧
            step program (q,t) = some (.inl (TM1to1.trTape enc0 mid.Tape).head) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
  let S := support0 tm alphabet enc dec
  have hs : TM0.Supports M (S : Set _) := support0_correct tm alphabet enc dec
  obtain ⟨program,hvalid,hprogram⟩ :=
    Shared.ComplexityBridge.TM0FiniteFullTape.finite_program_full_tape M S hs
  refine ⟨program,hvalid,?_⟩
  intro bits n last hrun htime hhalt
  obtain ⟨k,_,hk,mid,hrel,hr,hh⟩ :=
    halt_bounded tm alphabet enc dec enc0 encdec clock bits n last hrun htime hhalt
  let final := TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)
  obtain ⟨d,hd,q,t,htape,heq,hstep⟩ := hprogram (inputBits tm enc bits) k final hr hh
  have hfinal : final.Tape = TM1to1.trTape enc0 mid.Tape := by cases mid; rfl
  rw [hfinal] at heq hstep
  refine ⟨d,?_,mid,q,t,hrel,htape,heq,hstep⟩
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

end Shared.ComplexityBridge.TM2BinaryFullTape
