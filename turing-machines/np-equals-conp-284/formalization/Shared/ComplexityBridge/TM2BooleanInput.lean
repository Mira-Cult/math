import Shared.ComplexityBridge.TM2BooleanOutput
import Shared.ComplexityBridge.ClockBounds

/-! Finite numeric input initialization and a forward, fixed-block-clock
coverage theorem for the canonical P class. Uniform interpreter computability,
bit-cost and binary-machine simulation obligations are not assumed or
discharged by this file. `TM2Primcodable` proves decoder computability. -/
namespace Shared.Codes.TM2Program
open Shared.Codes.TM2StatementExecution

theorem run_halted_more (p : Program) (m extra : Nat) (c r : Result)
    (h : run p m c = .halted r) : run p (m + extra) c = .halted r := by
  induction m generalizing c with
  | zero =>
    cases hl : c.label with
    | none =>
      have he : c = r := by simpa [run, hl] using h
      subst r
      cases extra <;> simp [run, hl]
    | some l => simp [run, hl] at h
  | succ m ih =>
    cases hl : c.label with
    | none =>
      have he : c = r := by simpa [run, hl] using h
      subst r
      rw [Nat.succ_add]
      simp [run, hl]
    | some l =>
      cases hp : p[l]? with
      | none => simp [run, hl, hp] at h
      | some q =>
        cases he : exec q c.state c.memory with
        | none => simp [run, hl, hp, he] at h
        | some d =>
          have hh : run p m d = .halted r := by simpa [run, hl, hp, he] using h
          have hh' := ih d hh
          simpa [Nat.succ_add, run, hl, hp, he] using hh'

theorem run_halted_mono (p : Program) {m n : Nat} (c r : Result)
    (hle : m ≤ n) (h : run p m c = .halted r) : run p n c = .halted r := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact run_halted_more p m extra c r h
end Shared.Codes.TM2Program

namespace Shared.ComplexityBridge.TM2BooleanInput
open Shared.ComplexityBridge.TM2Reification
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2Program

structure InputData where
  stackCount : Nat
  states : Nat
  symbols : Nat
  labels : Nat
  main : Nat
  initialState : Nat
  inputStack : Nat
  falseSymbol : Nat
  trueSymbol : Nat
  deriving DecidableEq, Repr

def validInputData (d : InputData) : Bool :=
  (d.main < d.labels) && (d.initialState < d.states) && (d.inputStack < d.stackCount) &&
    (d.falseSymbol < d.symbols) && (d.trueSymbol < d.symbols) && (d.falseSymbol != d.trueSymbol)

def inputBit (z o : Nat) (b : Bool) : Nat := if b then o else z

/-- Construct a finite configuration only after checking all fixed parameters. -/
def buildStart (d : InputData) (bits : List Bool) : Option Result :=
  if validInputData d then
    some ⟨some d.main, d.initialState,
      (List.replicate d.stackCount []).set d.inputStack (bits.map (inputBit d.falseSymbol d.trueSymbol))⟩
  else none

def inputSymbol {βΓ : Type} (aux : Turing.TM2ComputableAux Bool βΓ)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (b : Bool) : Nat :=
  (N.symbol aux.tm.k₀ (aux.inputAlphabet.symm b)).val

theorem inputSymbols_ne {βΓ : Type} (aux : Turing.TM2ComputableAux Bool βΓ)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) : inputSymbol aux N false ≠ inputSymbol aux N true := by
  intro h
  have hs : N.symbol aux.tm.k₀ (aux.inputAlphabet.symm false) =
      N.symbol aux.tm.k₀ (aux.inputAlphabet.symm true) := Fin.ext h
  have hi := (N.symbol aux.tm.k₀).injective hs
  have hb := congrArg aux.inputAlphabet hi
  simp at hb

def inputData {βΓ : Type} (aux : Turing.TM2ComputableAux Bool βΓ)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) : InputData :=
  ⟨N.stackCount, N.states, N.symbols, N.labels, (N.label aux.tm.main).val,
    (N.state aux.tm.initialState).val, (N.stack aux.tm.k₀).val,
    inputSymbol aux N false, inputSymbol aux N true⟩

theorem inputData_valid {βΓ : Type} (aux : Turing.TM2ComputableAux Bool βΓ)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) : validInputData (inputData aux N) = true := by
  have hfalse : inputSymbol aux N false < N.symbols :=
    Nat.lt_of_lt_of_le (N.symbol aux.tm.k₀ (aux.inputAlphabet.symm false)).isLt (N.symbol_bound aux.tm.k₀)
  have htrue : inputSymbol aux N true < N.symbols :=
    Nat.lt_of_lt_of_le (N.symbol aux.tm.k₀ (aux.inputAlphabet.symm true)).isLt (N.symbol_bound aux.tm.k₀)
  simp [validInputData, inputData, (N.label aux.tm.main).isLt,
    (N.state aux.tm.initialState).isLt, (N.stack aux.tm.k₀).isLt, hfalse, htrue, inputSymbols_ne aux N]

theorem inputBit_eq {βΓ : Type} (aux : Turing.TM2ComputableAux Bool βΓ)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (b : Bool) :
    inputBit (inputSymbol aux N false) (inputSymbol aux N true) b = inputSymbol aux N b := by
  cases b <;> rfl

theorem encodeInit_memory {βΓ : Type} (aux : Turing.TM2ComputableAux Bool βΓ)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (bits : List Bool) :
    encodeStacks N (Turing.initList aux.tm (bits.map aux.inputAlphabet.invFun)).stk =
      (List.replicate N.stackCount []).set (N.stack aux.tm.k₀).val
        (bits.map (inputBit (inputSymbol aux N false) (inputSymbol aux N true))) := by
  apply List.ext_getElem
  · simp [encodeStacks]
  · intro i hi hj
    have hi' : i < N.stackCount := by simpa [encodeStacks] using hi
    let k := N.stack.symm ⟨i, hi'⟩
    have hk : (N.stack k).val = i := by simp [k]
    by_cases heq : k = aux.tm.k₀
    · subst k
      have hidx : i = (N.stack aux.tm.k₀).val := by simpa [heq] using hk.symm
      subst i
      simp only [encodeStacks, List.getElem_ofFn]
      rw [N.stack.symm_apply_apply]
      rw [Shared.ComplexityBridge.TM2Symbols.initList_input]
      simp [inputSymbol, inputBit, List.map_map, Function.comp_def]
    · have hidx : i ≠ (N.stack aux.tm.k₀).val := by
        intro h
        apply heq
        apply stackCode_injective N
        simpa [hk] using h
      simp only [encodeStacks, List.getElem_ofFn]
      change ((Turing.initList aux.tm (bits.map aux.inputAlphabet.invFun)).stk k).map
        (fun x => (N.symbol k x).val) = _
      rw [Shared.ComplexityBridge.TM2Symbols.initList_other _ _ _ heq]
      rw [List.getElem_set_ne (Ne.symm hidx) hj]
      simp

theorem buildStart_eq {βΓ : Type} (aux : Turing.TM2ComputableAux Bool βΓ)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (bits : List Bool) :
    buildStart (inputData aux N) bits =
      some (encodeConfig N (Turing.initList aux.tm (bits.map aux.inputAlphabet.invFun))) := by
  unfold buildStart
  rw [inputData_valid aux N]
  simp only [↓reduceIte]
  change some (⟨some (N.label aux.tm.main).val, (N.state aux.tm.initialState).val,
    (List.replicate N.stackCount []).set (N.stack aux.tm.k₀).val
      (bits.map (inputBit (inputSymbol aux N false) (inputSymbol aux N true)))⟩ : Result) =
    some (⟨some (N.label aux.tm.main).val, (N.state aux.tm.initialState).val,
      encodeStacks N (Turing.initList aux.tm (bits.map aux.inputAlphabet.invFun)).stk⟩ : Result)
  rw [encodeInit_memory aux N bits]

/-- Numeric input-symbol mapping is primitive recursive on finite data. -/
theorem inputBit_primrec : Primrec (fun p : (Nat × Nat) × Bool => inputBit p.1.1 p.1.2 p.2) := by
  have hb : Primrec (fun p : (Nat × Nat) × Bool => p.2) := Primrec.snd
  have hz : Primrec (fun p : (Nat × Nat) × Bool => p.1.1) := Primrec.fst.comp Primrec.fst
  have ho : Primrec (fun p : (Nat × Nat) × Bool => p.1.2) := Primrec.snd.comp Primrec.fst
  apply (Primrec.cond hb ho hz).of_eq
  rintro ⟨⟨z, o⟩, b⟩
  cases b <;> rfl

def encodeBits (p : (Nat × Nat) × List Bool) : List Nat :=
  p.2.map (inputBit p.1.1 p.1.2)

theorem encodeBits_primrec : Primrec encodeBits := by
  have harg : Primrec₂ (fun (p : (Nat × Nat) × List Bool) (b : Bool) =>
      inputBit p.1.1 p.1.2 b) :=
    (inputBit_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  exact Primrec.list_map Primrec.snd harg

def emptyStacks (n : Nat) : Stacks := List.replicate n []

theorem emptyStacks_primrec : Primrec emptyStacks := by
  have hstep : Primrec₂ (fun (_ : Nat) (s : Stacks) => ([] : List Nat) :: s) :=
    (Primrec.list_cons.comp (Primrec.const []) Primrec.snd).to₂
  have h := Primrec.nat_rec₁ ([] : Stacks) hstep
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [emptyStacks, List.replicate_succ, ih]

def buildMemory (p : (Nat × Nat) × ((Nat × Nat) × List Bool)) : Stacks :=
  (emptyStacks p.1.1).set p.1.2 (encodeBits p.2)

theorem buildMemory_primrec : Primrec buildMemory := by
  let Arg := (Nat × Nat) × ((Nat × Nat) × List Bool)
  have hn : Primrec (fun p : Arg => p.1.1) := Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : Arg => p.1.2) := Primrec.snd.comp Primrec.fst
  have hb : Primrec (fun p : Arg => encodeBits p.2) := encodeBits_primrec.comp Primrec.snd
  have he : Primrec (fun p : Arg => emptyStacks p.1.1) := emptyStacks_primrec.comp hn
  exact Primrec.list_set.comp he (Primrec.pair hi hb)

/-- A balanced tuple representation whose numeric encoding is already
primitive recursive in mathlib. -/
abbrev InputRaw := (Nat × Nat × Nat) × (Nat × Nat × Nat) × (Nat × Nat × Nat)
abbrev ResultRaw := Option Nat × Nat × Stacks

def inputRaw (d : InputData) : InputRaw :=
  ((d.stackCount, d.states, d.symbols), (d.labels, d.main, d.initialState),
    (d.inputStack, d.falseSymbol, d.trueSymbol))

def resultRaw (r : Result) : ResultRaw := (r.label, r.state, r.memory)

def validRaw (d : InputRaw) : Bool :=
  (d.2.1.2.1 < d.2.1.1) && (d.2.1.2.2 < d.1.2.1) && (d.2.2.1 < d.1.1) &&
    (d.2.2.2.1 < d.1.2.2) && (d.2.2.2.2 < d.1.2.2) && (d.2.2.2.1 != d.2.2.2.2)

def buildRaw (p : InputRaw × List Bool) : Option ResultRaw :=
  if validRaw p.1 then
    some (some p.1.2.1.2.1, p.1.2.1.2.2,
      buildMemory ((p.1.1.1, p.1.2.2.1), (p.1.2.2.2.1, p.1.2.2.2.2), p.2))
  else none

theorem validRaw_primrec : Primrec validRaw := by
  have hA : Primrec (fun d : InputRaw => d.1) := Primrec.fst
  have hB : Primrec (fun d : InputRaw => d.2.1) := Primrec.fst.comp Primrec.snd
  have hC : Primrec (fun d : InputRaw => d.2.2) := Primrec.snd.comp Primrec.snd
  have hks : Primrec (fun d : InputRaw => d.1.1) := Primrec.fst.comp hA
  have hstates : Primrec (fun d : InputRaw => d.1.2.1) := (Primrec.fst.comp Primrec.snd).comp hA
  have hsymbols : Primrec (fun d : InputRaw => d.1.2.2) := (Primrec.snd.comp Primrec.snd).comp hA
  have hlabels : Primrec (fun d : InputRaw => d.2.1.1) := Primrec.fst.comp hB
  have hmain : Primrec (fun d : InputRaw => d.2.1.2.1) := (Primrec.fst.comp Primrec.snd).comp hB
  have hstate : Primrec (fun d : InputRaw => d.2.1.2.2) := (Primrec.snd.comp Primrec.snd).comp hB
  have hstack : Primrec (fun d : InputRaw => d.2.2.1) := Primrec.fst.comp hC
  have hz : Primrec (fun d : InputRaw => d.2.2.2.1) := (Primrec.fst.comp Primrec.snd).comp hC
  have ho : Primrec (fun d : InputRaw => d.2.2.2.2) := (Primrec.snd.comp Primrec.snd).comp hC
  have h1 := (Primrec.nat_lt.comp hmain hlabels).decide
  have h2 := (Primrec.nat_lt.comp hstate hstates).decide
  have h3 := (Primrec.nat_lt.comp hstack hks).decide
  have h4 := (Primrec.nat_lt.comp hz hsymbols).decide
  have h5 := (Primrec.nat_lt.comp ho hsymbols).decide
  have h6 := Primrec.not.comp (Primrec.beq.comp hz ho)
  have ht := Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp h1 h2) h3) h4) h5) h6
  apply ht.of_eq
  intro d
  simp [validRaw, bne]

theorem buildRaw_primrec : Primrec buildRaw := by
  let Arg := InputRaw × List Bool
  have hA : Primrec (fun p : Arg => p.1.1) := Primrec.fst.comp Primrec.fst
  have hB : Primrec (fun p : Arg => p.1.2.1) := (Primrec.fst.comp Primrec.snd).comp Primrec.fst
  have hC : Primrec (fun p : Arg => p.1.2.2) := (Primrec.snd.comp Primrec.snd).comp Primrec.fst
  have hks : Primrec (fun p : Arg => p.1.1.1) := Primrec.fst.comp hA
  have hmain : Primrec (fun p : Arg => p.1.2.1.2.1) := (Primrec.fst.comp Primrec.snd).comp hB
  have hstate : Primrec (fun p : Arg => p.1.2.1.2.2) := (Primrec.snd.comp Primrec.snd).comp hB
  have hstack : Primrec (fun p : Arg => p.1.2.2.1) := Primrec.fst.comp hC
  have hz : Primrec (fun p : Arg => p.1.2.2.2.1) := (Primrec.fst.comp Primrec.snd).comp hC
  have ho : Primrec (fun p : Arg => p.1.2.2.2.2) := (Primrec.snd.comp Primrec.snd).comp hC
  have hm : Primrec (fun p : Arg => buildMemory ((p.1.1.1, p.1.2.2.1),
      (p.1.2.2.2.1, p.1.2.2.2.2), p.2)) :=
    buildMemory_primrec.comp (Primrec.pair (Primrec.pair hks hstack) (Primrec.pair (Primrec.pair hz ho) Primrec.snd))
  have hr : Primrec (fun p : Arg => (some p.1.2.1.2.1, p.1.2.1.2.2,
      buildMemory ((p.1.1.1, p.1.2.2.1), (p.1.2.2.2.1, p.1.2.2.2.2), p.2))) :=
    Primrec.pair (Primrec.option_some.comp hmain) (Primrec.pair hstate hm)
  have hv : Primrec (fun p : Arg => validRaw p.1) := validRaw_primrec.comp Primrec.fst
  have hc : Primrec (fun p : Arg => bif validRaw p.1 then
      some (some p.1.2.1.2.1, p.1.2.1.2.2,
        buildMemory ((p.1.1.1, p.1.2.2.1), (p.1.2.2.2.1, p.1.2.2.2.2), p.2))
    else none) := Primrec.cond hv (Primrec.option_some.comp hr) (Primrec.const (none : Option ResultRaw))
  apply hc.of_eq
  rintro ⟨d, bits⟩
  cases h : validRaw d <;> simp [buildRaw, h]

theorem buildRaw_computable : Computable buildRaw := buildRaw_primrec.to_comp

theorem buildRaw_eq (d : InputData) (bits : List Bool) :
    buildRaw (inputRaw d, bits) = (buildStart d bits).map resultRaw := by
  have hv : validRaw (inputRaw d) = validInputData d := rfl
  unfold buildRaw
  rw [hv]
  cases h : validInputData d <;>
    simp [h, buildStart, inputRaw, resultRaw, buildMemory, emptyStacks, encodeBits]

/-- A canonical polynomial-time Boolean function has fixed finite input
parameters and a finite numeric program. The initial bitstring is the actual
library encoding; all other initial stacks are empty. -/
theorem canonicalPoly_boolean_io {α : Type} [BitstringEncoding α]
    (f : α → Bool) (hf : ComplexityTheory.IsPolyTime f) :
    ∃ (h : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := α))
        (BitstringEncoding.bitEncode (α := Bool)) f)
      (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Shared.Codes.TM2Statements.Code)
      (e : Nat) (d : InputData),
      decodeProgram e = some p ∧ d = inputData h.toTM2ComputableAux N ∧
      programValid p N.stackCount N.states N.symbols = true ∧
      ∀ a, ∃ start r, buildStart d (BitstringEncoding.bitEncode a) = some start ∧
        run p (h.time.eval (BitstringEncoding.bitEncode a).length) start = .halted r ∧
        CfgRel N (Turing.haltList h.tm
          ((BitstringEncoding.bitEncode (f a)).map h.outputAlphabet.invFun)) (erase r) ∧
        Shared.ComplexityBridge.TM2BooleanOutput.extractMemory
          (Shared.ComplexityBridge.TM2BooleanOutput.outputSymbol h.toTM2ComputableAux N false,
           Shared.ComplexityBridge.TM2BooleanOutput.outputSymbol h.toTM2ComputableAux N true,
           (N.stack h.tm.k₁).val, r.label, r.memory) = some (f a) := by
  obtain ⟨h, N, p, e, he, hp, hv, hr⟩ :=
    Shared.ComplexityBridge.TM2BooleanOutput.canonicalPoly_boolean_output f hf
  refine ⟨h, N, p, e, inputData h.toTM2ComputableAux N, he, rfl, hv, ?_⟩
  intro a
  obtain ⟨r, hrun, hrel, hout⟩ := hr a
  refine ⟨encodeConfig N (Turing.initList h.tm
    ((BitstringEncoding.bitEncode a).map h.inputAlphabet.invFun)), r, ?_, hrun, hrel, hout⟩
  exact buildStart_eq h.toTM2ComputableAux N (BitstringEncoding.bitEncode a)

/-- A canonical polynomial-time Boolean function has fixed finite codes,
a primitive-recursive initializer and one fixed block-clock exponent. -/
theorem canonicalPoly_boolean_numericClock {α : Type} [BitstringEncoding α]
    (f : α → Bool) (hf : ComplexityTheory.IsPolyTime f) :
    ∃ (h : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := α))
        (BitstringEncoding.bitEncode (α := Bool)) f)
      (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Shared.Codes.TM2Statements.Code)
      (e : Nat) (d : InputData) (z o out k : Nat),
      decodeProgram e = some p ∧ validInputData d = true ∧
      programValid p N.stackCount N.states N.symbols = true ∧
      z = Shared.ComplexityBridge.TM2BooleanOutput.outputSymbol h.toTM2ComputableAux N false ∧
      o = Shared.ComplexityBridge.TM2BooleanOutput.outputSymbol h.toTM2ComputableAux N true ∧
      out = (N.stack h.tm.k₁).val ∧
      ∀ a, ∃ start r, buildRaw (inputRaw d, BitstringEncoding.bitEncode a) = some (resultRaw start) ∧
        run p (((BitstringEncoding.bitEncode a).length + 2) ^ k) start = .halted r ∧
        CfgRel N (Turing.haltList h.tm
          ((BitstringEncoding.bitEncode (f a)).map h.outputAlphabet.invFun)) (erase r) ∧
        Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (z, o, out, r.label, r.memory) = some (f a) := by
  obtain ⟨h, N, p, e, d, he, hd, hv, hr⟩ := canonicalPoly_boolean_io f hf
  obtain ⟨k, hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent h.time
  let z := Shared.ComplexityBridge.TM2BooleanOutput.outputSymbol h.toTM2ComputableAux N false
  let o := Shared.ComplexityBridge.TM2BooleanOutput.outputSymbol h.toTM2ComputableAux N true
  let out := (N.stack h.tm.k₁).val
  have hvalid : validInputData d = true := by rw [hd]; exact inputData_valid h.toTM2ComputableAux N
  refine ⟨h, N, p, e, d, z, o, out, k, he, hvalid, hv, rfl, rfl, rfl, ?_⟩
  intro a
  obtain ⟨start, r, hstart, hrun, hrel, hout⟩ := hr a
  refine ⟨start, r, ?_, ?_, hrel, hout⟩
  · rw [buildRaw_eq, hstart]; rfl
  · exact Shared.Codes.TM2Program.run_halted_mono p start r (hk (BitstringEncoding.bitEncode a).length) hrun

/-- Absorb the library's threefold list encoding into a fixed raw-input
exponent, uniformly including the empty input. -/
theorem threeLength_clock_bound (n k : Nat) : (3 * n + 2) ^ k ≤ (n + 2) ^ (2 * k) := by
  have hbase : 3 * n + 2 ≤ (n + 2) ^ 2 := by
    simp only [pow_two, Nat.add_mul, Nat.mul_add]
    omega
  calc
    (3 * n + 2) ^ k ≤ ((n + 2) ^ 2) ^ k := Nat.pow_le_pow_left hbase k
    _ = (n + 2) ^ (2 * k) := by rw [pow_mul]

/-- One-way coverage from the canonical P class to fixed-clock numeric
programs, measured in complete TM2 statement blocks. -/
theorem canonicalP_numericClock (L : ComplexityTheory.DecisionProblem)
    (hL : L ∈ ComplexityTheory.P) :
    ∃ (h : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := List Bool))
        (BitstringEncoding.bitEncode (α := Bool)) L)
      (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Shared.Codes.TM2Statements.Code)
      (e : Nat) (d : InputData) (z o out k : Nat),
      decodeProgram e = some p ∧ validInputData d = true ∧
      programValid p N.stackCount N.states N.symbols = true ∧
      ∀ x, ∃ start r, buildRaw (inputRaw d, BitstringEncoding.bitEncode x) = some (resultRaw start) ∧
        run p ((x.length + 2) ^ k) start = .halted r ∧
        CfgRel N (Turing.haltList h.tm
          ((BitstringEncoding.bitEncode (L x)).map h.outputAlphabet.invFun)) (erase r) ∧
        Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (z, o, out, r.label, r.memory) = some (L x) := by
  have hp : ComplexityTheory.IsPolyTime L := hL
  obtain ⟨h, N, p, e, d, z, o, out, k, he, hd, hv, hz, ho, hout, hr⟩ :=
    canonicalPoly_boolean_numericClock L hp
  refine ⟨h, N, p, e, d, z, o, out, 2 * k, he, hd, hv, ?_⟩
  intro x
  obtain ⟨start, r, hstart, hrun, hrel, houtput⟩ := hr x
  refine ⟨start, r, hstart, ?_, hrel, houtput⟩
  have hclock : ((BitstringEncoding.bitEncode x).length + 2) ^ k ≤ (x.length + 2) ^ (2 * k) := by
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length]
    exact threeLength_clock_bound x.length k
  exact Shared.Codes.TM2Program.run_halted_mono p start r hclock hrun

example : buildStart ⟨1, 1, 2, 1, 0, 0, 0, 0, 1⟩ [] =
    some ⟨some 0, 0, [[]]⟩ := by decide
example : buildStart ⟨1, 1, 2, 1, 0, 0, 0, 0, 0⟩ [] = none := by decide
example : buildStart ⟨1, 1, 2, 1, 0, 0, 1, 0, 1⟩ [] = none := by decide
example : buildRaw (inputRaw ⟨1, 1, 2, 1, 0, 0, 0, 0, 1⟩, []) =
    some (some 0, 0, [[]]) := by decide
example : buildRaw (inputRaw ⟨1, 1, 2, 1, 0, 0, 0, 0, 0⟩, []) = none := by decide

end Shared.ComplexityBridge.TM2BooleanInput
