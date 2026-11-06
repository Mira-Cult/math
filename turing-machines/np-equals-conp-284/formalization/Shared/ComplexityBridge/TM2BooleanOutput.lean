import Shared.ComplexityBridge.TM2Reification

/-! Boolean output extraction from reified TM2 configurations. The extractor
rejects duplicate Boolean codes, non-singleton output and non-halted labels.
It does not by itself verify state reset or cleanup of other stacks; the
canonical theorem retains the full library halt-configuration relation. -/
namespace Shared.ComplexityBridge.TM2BooleanOutput
open Shared.ComplexityBridge.TM2Reification
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2Program

/-- The two symbol codes must be distinct, and the output must be a singleton.
No default answer is assigned to malformed data. -/
def decodeStack (p : Nat × Nat × List Nat) : Option Bool :=
  if p.1 = p.2.1 then none
  else if p.2.2 = [p.1] then some false
  else if p.2.2 = [p.2.1] then some true
  else none

theorem decodeStack_primrec : Primrec decodeStack := by
  let Arg := Nat × Nat × List Nat
  have hzero : Primrec (fun p : Arg => p.1) := Primrec.fst
  have hone : Primrec (fun p : Arg => p.2.1) := Primrec.fst.comp Primrec.snd
  have hxs : Primrec (fun p : Arg => p.2.2) := Primrec.snd.comp Primrec.snd
  have hzlist : Primrec (fun p : Arg => [p.1]) := Primrec.list_cons.comp hzero (Primrec.const [])
  have holist : Primrec (fun p : Arg => [p.2.1]) := Primrec.list_cons.comp hone (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp hzero hone) (Primrec.const none)
    (Primrec.ite (Primrec.eq.comp hxs hzlist) (Primrec.const (some false))
      (Primrec.ite (Primrec.eq.comp hxs holist) (Primrec.const (some true)) (Primrec.const none)))

theorem decodeStack_computable : Computable decodeStack := decodeStack_primrec.to_comp

theorem decodeStack_bit {z o : Nat} (hne : z ≠ o) (b : Bool) :
    decodeStack (z, o, [if b then o else z]) = some b := by
  cases b <;> simp [decodeStack, hne, Ne.symm hne]

def outputSymbol {αΓ : Type} (aux : Turing.TM2ComputableAux αΓ Bool)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (b : Bool) : Nat :=
  (N.symbol aux.tm.k₁ (aux.outputAlphabet.symm b)).val

theorem outputSymbols_ne {αΓ : Type} (aux : Turing.TM2ComputableAux αΓ Bool)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) :
    outputSymbol aux N false ≠ outputSymbol aux N true := by
  intro h
  have hs : N.symbol aux.tm.k₁ (aux.outputAlphabet.symm false) =
      N.symbol aux.tm.k₁ (aux.outputAlphabet.symm true) := Fin.ext h
  have hi := (N.symbol aux.tm.k₁).injective hs
  have hb := congrArg aux.outputAlphabet hi
  simp at hb

/-- The result is decoded from the actual output stack in a configuration
related to the complete mathlib halt configuration. -/
theorem related_halt_decodes {αΓ : Type} (aux : Turing.TM2ComputableAux αΓ Bool)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (r : Result) (b : Bool)
    (hr : CfgRel N (Turing.haltList aux.tm [aux.outputAlphabet.symm b]) (erase r)) :
    decodeStack (outputSymbol aux N false, outputSymbol aux N true,
      stackFn r.memory (N.stack aux.tm.k₁).val) = some b := by
  have hs := hr.2.2 aux.tm.k₁
  change stackFn r.memory (N.stack aux.tm.k₁).val =
    ((Turing.haltList aux.tm [aux.outputAlphabet.symm b]).stk aux.tm.k₁).map
      (fun x => (N.symbol aux.tm.k₁ x).val) at hs
  rw [Shared.ComplexityBridge.TM2Symbols.haltList_output] at hs
  have hstack : stackFn r.memory (N.stack aux.tm.k₁).val =
      [if b then outputSymbol aux N true else outputSymbol aux N false] := by
    cases b <;> simpa [outputSymbol] using hs
  rw [hstack]
  exact decodeStack_bit (outputSymbols_ne aux N) b

/-- Decode only a halted configuration's output stack. This extracts a
Boolean; it is not by itself a certificate that all other stacks were cleaned. -/
def extractOutput (p : (Nat × Nat × List Nat) × Option Nat) : Option Bool :=
  if p.2.isSome then none else decodeStack p.1

theorem stackFn_primrec : Primrec₂ stackFn := by
  have h : Primrec (fun p : Stacks × Nat => stackFn p.1 p.2) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const [])
  exact h.to₂

theorem extractOutput_primrec : Primrec extractOutput := by
  let Arg := (Nat × Nat × List Nat) × Option Nat
  have ht : Primrec (fun p : Arg => p.2.isSome) := Primrec.option_isSome.comp Primrec.snd
  have hv : Primrec (fun p : Arg => decodeStack p.1) := decodeStack_primrec.comp Primrec.fst
  have hn : Primrec (fun _ : Arg => (none : Option Bool)) := Primrec.const none
  apply (Primrec.cond ht hn hv).of_eq
  rintro ⟨input, label⟩
  cases label <;> rfl

theorem extractOutput_computable : Computable extractOutput := extractOutput_primrec.to_comp

/-- Combine finite stack lookup with the halted Boolean decoder. -/
def extractMemory (p : Nat × Nat × Nat × Option Nat × Stacks) : Option Bool :=
  extractOutput ((p.1, p.2.1, stackFn p.2.2.2.2 p.2.2.1), p.2.2.2.1)

theorem extractMemory_primrec : Primrec extractMemory := by
  let Arg := Nat × Nat × Nat × Option Nat × Stacks
  have hz : Primrec (fun p : Arg => p.1) := Primrec.fst
  have ho : Primrec (fun p : Arg => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : Arg => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun p : Arg => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm : Primrec (fun p : Arg => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hstk : Primrec (fun p : Arg => stackFn p.2.2.2.2 p.2.2.1) := stackFn_primrec.comp hm hi
  have htuple : Primrec (fun p : Arg => ((p.1, p.2.1, stackFn p.2.2.2.2 p.2.2.1), p.2.2.2.1)) :=
    Primrec.pair (Primrec.pair hz (Primrec.pair ho hstk)) hl
  exact extractOutput_primrec.comp htuple

theorem extractMemory_computable : Computable extractMemory := extractMemory_primrec.to_comp

theorem related_halt_extracts {αΓ : Type} (aux : Turing.TM2ComputableAux αΓ Bool)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (r : Result) (b : Bool)
    (hr : CfgRel N (Turing.haltList aux.tm [aux.outputAlphabet.symm b]) (erase r)) :
    extractMemory (outputSymbol aux N false, outputSymbol aux N true,
      (N.stack aux.tm.k₁).val, r.label, r.memory) = some b := by
  have hl : r.label = none := by simpa [CfgRel, erase, Turing.haltList] using hr.1
  simpa [extractMemory, extractOutput, hl] using related_halt_decodes aux N r b hr

/-- A canonical polynomial-time Boolean function has a numeric program whose
actual output stack decodes to its result. The code and numberings are supplied
by an existence proof, not by runtime access to the function. -/
theorem canonicalPoly_boolean_output {α : Type} [BitstringEncoding α]
    (f : α → Bool) (hf : ComplexityTheory.IsPolyTime f) :
    ∃ (h : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := α))
        (BitstringEncoding.bitEncode (α := Bool)) f)
      (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Shared.Codes.TM2Statements.Code) (e : Nat),
      decodeProgram e = some p ∧ p = reifyProgram N h.tm.m ∧
      programValid p N.stackCount N.states N.symbols = true ∧
      ∀ a, ∃ r, run p (h.time.eval (BitstringEncoding.bitEncode a).length)
          (encodeConfig N (Turing.initList h.tm
            ((BitstringEncoding.bitEncode a).map h.inputAlphabet.invFun))) = .halted r ∧
        CfgRel N (Turing.haltList h.tm
          ((BitstringEncoding.bitEncode (f a)).map h.outputAlphabet.invFun)) (erase r) ∧
        extractMemory (outputSymbol h.toTM2ComputableAux N false,
          outputSymbol h.toTM2ComputableAux N true,
          (N.stack h.tm.k₁).val, r.label, r.memory) = some (f a) := by
  obtain ⟨h, N, p, e, he, hp, hv, hr⟩ := canonicalPoly_numeric f hf
  refine ⟨h, N, p, e, he, hp, hv, ?_⟩
  intro a
  obtain ⟨r, hrun, hrel⟩ := hr a
  refine ⟨r, hrun, hrel, ?_⟩
  apply related_halt_extracts h.toTM2ComputableAux N r (f a)
  exact hrel

example : decodeStack (0, 1, [0]) = some false := by decide
example : decodeStack (0, 1, [1]) = some true := by decide
example : decodeStack (0, 0, [0]) = none := by decide
example : decodeStack (0, 1, []) = none := by decide
example : decodeStack (0, 1, [0, 1]) = none := by decide
example : decodeStack (0, 1, [2]) = none := by decide
example : extractMemory (0, 1, 0, none, [[1]]) = some true := by decide
example : extractMemory (0, 1, 0, some 0, [[1]]) = none := by decide
example : extractMemory (0, 1, 1, none, [[1]]) = none := by decide

end Shared.ComplexityBridge.TM2BooleanOutput
