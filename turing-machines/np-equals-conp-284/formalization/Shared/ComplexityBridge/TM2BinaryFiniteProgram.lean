import Shared.ComplexityBridge.TM2BinaryPostCosts
import Shared.ComplexityBridge.TM0FiniteReindex

/-! Compose finite-control reindexing with the binary simulation. The result
runs on the serialized TM2 initial tape and returns one encoded head bit;
raw input preprocessing and Boolean output decoding are not yet compiled. -/
namespace Shared.ComplexityBridge.TM2BinaryFiniteProgram
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2GeneralTM1Costs
open Shared.ComplexityBridge.TM2GeneralTM0Costs
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms

variable (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
variable {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
variable (dec : List.Vector Bool width → Alphabet tm)
variable (enc0 : enc default = List.Vector.replicate width false)
variable (encdec : ∀ a, dec (enc a) = a)

include encdec

/-- One finite program, independent of input and run length, simulates every
polynomially bounded halted TM2 run on its serialized initial tape. Its
Boolean result is the head bit of the binary encoded final tape. -/
theorem finite_program (p : Polynomial Nat) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ program : Program, valid program = true ∧
      ∀ (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg),
        runSteps tm.step n (Turing.initList tm bits) = some last →
        n ≤ p.eval bits.length → last.l = none →
        ∃ mid, TM2to1.TrCfg last mid ∧
          bounded program (inputBits tm enc bits)
            ((2 * timePolynomial tm alphabet enc dec p + 1).eval bits.length) =
              some ((TM1to1.trTape enc0 mid.Tape).head) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
  let S := support0 tm alphabet enc dec
  have hs : TM0.Supports M (S : Set _) := support0_correct tm alphabet enc dec
  obtain ⟨program,hvalid,hprogram⟩ := TM0FiniteReindex.finite_program M S hs
  refine ⟨program,hvalid,?_⟩
  intro bits n last hrun htime hhalt
  obtain ⟨d,hdlo,hdhi,mid,hrel,hr,hh⟩ :=
    halt_bounded tm alphabet enc dec enc0 encdec p bits n last hrun htime hhalt
  let final := TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)
  have hb := hprogram (inputBits tm enc bits) d final hr hh
  have hbits : final.Tape.head = (TM1to1.trTape enc0 mid.Tape).head := by cases mid; rfl
  rw [hbits] at hb
  obtain ⟨t,ht,hresult⟩ := (bounded_iff_result program (inputBits tm enc bits) (2*d+1) _).1 hb
  refine ⟨mid,hrel,?_⟩
  apply (bounded_iff_result program (inputBits tm enc bits) _ _).2
  refine ⟨t,?_,hresult⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

/-- The marker bit gives at least two source symbols, so any codec with a
left inverse has a positive width. -/
theorem width_positive : 0 < width := by
  by_contra hn
  have hw : width = 0 := by omega
  subst width
  let a : Alphabet tm := (false,fun _ => none)
  let b : Alphabet tm := (true,fun _ => none)
  have he : enc a = enc b := Subsingleton.elim _ _
  have h := congrArg dec he
  rw [encdec a,encdec b] at h
  have hh := congrArg Prod.fst h
  contradiction

theorem inputBits_length_ge (bits : List (tm.Γ tm.k₀)) :
    bits.length ≤ (inputBits tm enc bits).length := by
  rw [inputBits_length tm enc bits]
  have hw := width_positive tm enc dec encdec
  have hm : bits.length ≤ max bits.length 1 := le_max_left _ _
  have hp : max bits.length 1 ≤ width * max bits.length 1 := by
    simpa using Nat.mul_le_mul_right (max bits.length 1) hw
  omega

include alphabet

/-- The same finite program fits one fixed-exponent candidate clock for all
serialized inputs. This still returns the first encoded output bit. -/
theorem fixed_exponent_candidate (p : Polynomial Nat) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ candidate : Candidate, valid candidate.2 = true ∧ (∃ e, decode e = some candidate) ∧
      ∀ (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg),
        runSteps tm.step n (Turing.initList tm bits) = some last →
        n ≤ p.eval bits.length → last.l = none →
        ∃ mid, TM2to1.TrCfg last mid ∧
          evaluate candidate (inputBits tm enc bits) = some ((TM1to1.trTape enc0 mid.Tape).head) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨program,hvalid,hprogram⟩ := finite_program tm alphabet enc dec enc0 encdec p
  obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent
    (2*timePolynomial tm alphabet enc dec p+1)
  refine ⟨(k,program),hvalid,candidate_coverage (k,program) hvalid,?_⟩
  intro bits n last hrun htime hhalt
  obtain ⟨mid,hrel,hresult⟩ := hprogram bits n last hrun htime hhalt
  refine ⟨mid,hrel,?_⟩
  obtain ⟨t,ht,hout⟩ := (bounded_iff_result program (inputBits tm enc bits)
    ((2*timePolynomial tm alphabet enc dec p+1).eval bits.length) _).1 hresult
  change bounded program (inputBits tm enc bits) (((inputBits tm enc bits).length+2)^k) = _
  apply (bounded_iff_result program (inputBits tm enc bits) _ _).2
  refine ⟨t,le_trans ht (le_trans (hk bits.length) ?_),hout⟩
  exact Nat.pow_le_pow_left (by have hh := inputBits_length_ge tm enc dec encdec bits; omega) k

end Shared.ComplexityBridge.TM2BinaryFiniteProgram
