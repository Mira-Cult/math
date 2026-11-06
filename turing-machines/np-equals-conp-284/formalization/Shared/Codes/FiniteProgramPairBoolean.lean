import Shared.Codes.FiniteProgramPairContinuation
import Shared.ComplexityBridge.TM2BooleanTag
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false

/-! Combine the physical pair initializer and finite TM2 simulator with the
blank-preserving Boolean output tag. -/
namespace Shared.Codes.FiniteProgramPairBoolean
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2BooleanTag

/-- A fixed codec and a fixed finite evaluator work for every encoded pair.
If the source halts with exactly one of the two distinct output symbols, the
actual linked table returns the corresponding Boolean. The time includes the
initializer, its handoff, and the quantitative simulator fuel. Codec and table
existence for a function-valued TM2 is mathematical, not runtime reification. -/
theorem boolean_pair_evaluator (tm : Turing.FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
    [DecidableEq (tm.Γ tm.k₁)] (no yes : tm.Γ tm.k₁) (hne : no ≠ yes)
    (inp : tm.Γ tm.k₀ ≃ Bool) (p : Polynomial Nat) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ (width : Nat) (enc : Alphabet tm → List.Vector Bool width)
      (dec : List.Vector Bool width → Alphabet tm),
      enc default = List.Vector.replicate width false ∧ (∀ a, dec (enc a) = a) ∧
      ∃ eval : Program, valid eval = true ∧
        (let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
         let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
         let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
         let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
         valid (Shared.Codes.FiniteProgramPairContinuation.program mz mo z o width eval) = true) ∧
        ∀ (x w : List Bool) (n : Nat) (last : tm.Cfg) (b : Bool),
          let bits := (BitstringEncoding.bitEncode (x,w)).map inp.symm
          let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
          let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
          let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
          let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
          Shared.ComplexityBridge.TM2Symbols.runSteps tm.step n (Turing.initList tm bits) = some last →
          n ≤ p.eval bits.length → last.l = none →
          last.stk tm.k₁ = [if b then yes else no] →
          bounded (Shared.Codes.FiniteProgramPairContinuation.program mz mo z o width eval)
            (BitstringEncoding.bitEncode (x,w))
            (Shared.Codes.FiniteProgramPairUnified.runtime mz mo z o x w width + 2 +
              ((2*timePolynomial tm alphabet enc dec p+1).eval bits.length)) = some b := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨width,baseEnc,baseDec,hblank,hinv⟩ := codec_exists tm alphabet
  let encode := taggedEncode tm yes baseEnc
  let decode := taggedDecode tm baseDec
  have he0 : encode default = List.Vector.replicate (width+1) false := tagged_blank tm yes baseEnc hblank
  have heinv : ∀ a, decode (encode a) = a := tagged_roundtrip tm yes baseEnc baseDec hinv
  obtain ⟨eval,hvalid,hcomp⟩ := Shared.Codes.FiniteProgramPairContinuation.finite_tm2_evaluator
    tm alphabet encode decode he0 heinv inp p
  refine ⟨width+1,encode,decode,he0,heinv,eval,hvalid,?_,?_⟩
  · exact Shared.Codes.FiniteProgramPairContinuation.program_valid _ _ _ _ _ eval hvalid
  · intro x w n last b
    dsimp only
    intro hrun htime hhalt hout
    obtain ⟨mid,hrel,hresult⟩ := hcomp x w n last hrun htime hhalt
    have hhead := tagged_tape_head tm yes baseEnc he0 mid.Tape
    have htag := related_output_tag tm yes last mid hrel (if b then yes else no) hout
    change bounded _ _ _ = some ((Turing.TM1to1.trTape he0 mid.Tape).head) at hresult
    rw [hhead,htag] at hresult
    cases b <;> simp [hne] at hresult ⊢ <;> exact hresult


/-- If the source is already proved total with a uniform polynomial bound,
    one fixed linked table computes its Boolean relation on every canonical
    pair. Its displayed clock retains the exact charged initialization time. -/
theorem total_pair_evaluator (tm : Turing.FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
    [DecidableEq (tm.Γ tm.k₁)] (no yes : tm.Γ tm.k₁) (hne : no ≠ yes)
    (inp : tm.Γ tm.k₀ ≃ Bool) (p : Polynomial Nat) (R : List Bool → List Bool → Bool)
    (hsource : ∀ x w, ∃ n ≤ p.eval ((BitstringEncoding.bitEncode (x,w)).map inp.symm).length,
      Shared.ComplexityBridge.TM2Symbols.runSteps tm.step n
        (Turing.initList tm ((BitstringEncoding.bitEncode (x,w)).map inp.symm)) =
          some (Turing.haltList tm [if R x w then yes else no])) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ (width : Nat) (enc : Alphabet tm → List.Vector Bool width)
      (dec : List.Vector Bool width → Alphabet tm) (eval : Program),
      enc default = List.Vector.replicate width false ∧ (∀ a, dec (enc a) = a) ∧
      valid eval = true ∧
      (let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
       let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
       let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
       let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
       valid (Shared.Codes.FiniteProgramPairContinuation.program mz mo z o width eval) = true) ∧
      ∀ x w,
        let bits := (BitstringEncoding.bitEncode (x,w)).map inp.symm
        let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
        let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
        let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
        let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
        bounded (Shared.Codes.FiniteProgramPairContinuation.program mz mo z o width eval)
          (BitstringEncoding.bitEncode (x,w))
          (Shared.Codes.FiniteProgramPairUnified.runtime mz mo z o x w width + 2 +
            ((2*timePolynomial tm alphabet enc dec p+1).eval bits.length)) = some (R x w) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨width,enc,dec,hblank,hinv,eval,hvalid,hlinked,hcomp⟩ :=
    boolean_pair_evaluator tm alphabet no yes hne inp p
  refine ⟨width,enc,dec,eval,hblank,hinv,hvalid,hlinked,?_⟩
  intro x w
  obtain ⟨n,hn,hr⟩ := hsource x w
  apply hcomp x w n (Turing.haltList tm [if R x w then yes else no]) (R x w) hr hn
  · rfl
  · simp [Turing.haltList]

end Shared.Codes.FiniteProgramPairBoolean
