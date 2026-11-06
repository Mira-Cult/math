import Shared.ComplexityBridge.TM1BinaryCosts

/-! Quantitative composition through mathlib's binary alphabet reduction and
TM1-to-TM0 translation. Input loading and Boolean output extraction are
separate obligations. -/
namespace Shared.ComplexityBridge.TM1BinaryPostCosts
open Turing
open Shared.ComplexityBridge.TM2Symbols

variable {Γ Λ σ : Type} [Inhabited Γ] [Fintype Γ] [Inhabited Λ] [Inhabited σ]
variable {n : Nat} (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
variable (enc0 : enc default = List.Vector.replicate n false) (encdec : ∀ a, dec (enc a) = a)
variable (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)

/-- Concatenate one complete code word per original input symbol. -/
def encodedInput (symbols : List Γ) : List Bool := symbols.flatMap (fun a => (enc a).toList)

omit [Inhabited Γ] [Fintype Γ] in
theorem encodedInput_length (symbols : List Γ) :
    (encodedInput enc symbols).length = n * symbols.length := by
  simp [encodedInput,List.Vector.toList_length,Nat.mul_comm]

omit [Fintype Γ] in
/-- The library's encoded input tape is precisely the tape initialized from
this finite serialization, including empty input and blank tails. -/
theorem encodedInput_tape (symbols : List Γ) :
    TM1to1.trTape enc0 (Tape.mk₁ symbols) = Tape.mk₁ (encodedInput enc symbols) := by
  simp [Tape.mk₁,Tape.mk₂,TM1to1.trTape_mk',TM1to1.trTape',encodedInput]

noncomputable def binarySupport : Finset (TM1to1.Λ' Γ Λ σ) := TM1to1.trSupp M S

theorem binarySupport_correct (hs : TM1.Supports M S) :
    TM1.Supports (TM1to1.tr enc dec M) (binarySupport M S) :=
  TM1to1.tr_supports enc dec M hs

theorem binarySupport_mem (x : TM1.Cfg Γ Λ σ) (h : x.l ∈ S.insertNone) :
    (TM1to1.trCfg enc enc0 x).l ∈ (binarySupport M S).insertNone := by
  classical
  cases hx : x.l with
  | none => simp [TM1to1.trCfg,hx]
  | some q =>
    have hq : q ∈ S := by rw [hx] at h; exact Finset.some_mem_insertNone.1 h
    have hcfg : (TM1to1.trCfg enc enc0 x).l = some (TM1to1.Λ'.normal q) := by
      cases x with | mk l v T => simp only at hx; subst l; rfl
    rw [hcfg]
    apply Finset.some_mem_insertNone.2
    change TM1to1.Λ'.normal q ∈ TM1to1.trSupp M S
    simp only [TM1to1.trSupp,Finset.mem_biUnion]
    exact ⟨q,hq,Finset.mem_insert_self _ _⟩

noncomputable def postLimit : Nat :=
  TM1GeneralTM0Costs.statementLimit (TM1to1.tr enc dec M) (binarySupport M S)

include encdec

/-- A source run has a binary post-Turing run with an explicit linear bound.
Each target step is a real single-bit move or write. -/
theorem run_bounded (hs : TM1.Supports M S) (k : Nat)
    (x x' : TM1.Cfg Γ Λ σ) (hmem : x.l ∈ S.insertNone)
    (hrun : runSteps (TM1.step M) k x = some x') :
    ∃ d, k ≤ d ∧ d ≤ k * TM1BinaryCosts.writeLimit M S * postLimit enc dec M S ∧
      runSteps (TM0.step (TM1to0.tr (TM1to1.tr enc dec M))) d
        (TM1to0.trCfg (TM1to1.tr enc dec M) (TM1to1.trCfg enc enc0 x)) =
      some (TM1to0.trCfg (TM1to1.tr enc dec M) (TM1to1.trCfg enc enc0 x')) := by
  obtain ⟨j,hjlo,hjhi,hj⟩ := TM1BinaryCosts.run_bounded enc dec enc0 encdec M S hs k x x' hmem hrun
  have hsup := binarySupport_correct enc dec M S hs
  have hb := binarySupport_mem enc enc0 M S x hmem
  obtain ⟨d,hdlo,hdhi,hd⟩ := TM1GeneralTM0Costs.run_bounded (TM1to1.tr enc dec M)
    (binarySupport M S) hsup j (TM1to1.trCfg enc enc0 x) (TM1to1.trCfg enc enc0 x') hb hj
  refine ⟨d,by omega,?_,hd⟩
  change d ≤ j * postLimit enc dec M S at hdhi
  exact le_trans hdhi (Nat.mul_le_mul_right _ hjhi)

omit encdec in
/-- Halt is retained by both translations. -/
theorem translated_halt (x : TM1.Cfg Γ Λ σ) (h : x.l = none) :
    TM0.step (TM1to0.tr (TM1to1.tr enc dec M))
      (TM1to0.trCfg (TM1to1.tr enc dec M) (TM1to1.trCfg enc enc0 x)) = none := by
  cases x with
  | mk l v T => cases l with | none => rfl | some q => simp at h

end Shared.ComplexityBridge.TM1BinaryPostCosts
