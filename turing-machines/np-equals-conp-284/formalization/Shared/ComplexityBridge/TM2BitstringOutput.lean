import Shared.ComplexityBridge.TM2BooleanInput
import Shared.ComplexityBridge.CNFComputability
import Shared.Codes.TM2CheckedCandidate

/-! Decode arbitrary finite Boolean output stacks from the effective numeric
TM2 representation. Timing below counts whole TM2 statement blocks, not bit
operations or a single-tape simulation. -/
namespace Shared.ComplexityBridge.TM2BitstringOutput
open Shared.ComplexityBridge.TM2Reification Shared.ComplexityBridge.TM2BooleanInput
open Shared.ComplexityBridge.TM2BooleanOutput
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2Program

abbrev Arg := Nat × Nat × List Nat

def validSymbol (z o x : Nat) : Bool := (x == z) || (x == o)
def decodedBit (o x : Nat) : Bool := x == o

/-- Equal symbol codes and any unknown symbol fail; an empty output is valid
when the two codes are distinct. -/
def decodeStack (p : Arg) : Option (List Bool) :=
  if p.1 = p.2.1 then none
  else if p.2.2.all (validSymbol p.1 p.2.1) then
    some (p.2.2.map (decodedBit p.2.1))
  else none

theorem decodeStack_primrec : Primrec decodeStack := by
  let A := Arg
  have hz : Primrec (fun p : A => p.1) := Primrec.fst
  have ho : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have heach : Primrec₂ (fun (p : A) (x : Nat) => validSymbol p.1 p.2.1 x) := by
    have hx : Primrec (fun q : A × Nat => q.2) := Primrec.snd
    have hzero : Primrec (fun q : A × Nat => q.1.1) := hz.comp Primrec.fst
    have hone : Primrec (fun q : A × Nat => q.1.2.1) := ho.comp Primrec.fst
    exact (Primrec.or.comp (Primrec.beq.comp hx hzero) (Primrec.beq.comp hx hone)).to₂
  have hbit : Primrec₂ (fun (p : A) (x : Nat) => decodedBit p.2.1 x) := by
    exact (Primrec.beq.comp (Primrec.snd : Primrec (fun q : A × Nat => q.2))
      (ho.comp Primrec.fst)).to₂
  have hall : Primrec (fun p : A => p.2.2.all (validSymbol p.1 p.2.1)) :=
    Shared.ComplexityBridge.CNF.list_all_primrec hs heach
  have hmap : Primrec (fun p : A => p.2.2.map (decodedBit p.2.1)) := Primrec.list_map hs hbit
  have hc : Primrec (fun p : A => if p.2.2.all (validSymbol p.1 p.2.1) then
      some (p.2.2.map (decodedBit p.2.1)) else none) := by
    apply (Primrec.cond hall (Primrec.option_some.comp hmap) (Primrec.const none)).of_eq
    intro p
    cases p.2.2.all (validSymbol p.1 p.2.1) <;> simp
  exact Primrec.ite (Primrec.eq.comp hz ho) (Primrec.const none) hc

theorem decodeStack_computable : Computable decodeStack := decodeStack_primrec.to_comp

theorem decodeStack_encoded (z o : Nat) (hne : z ≠ o) (bits : List Bool) :
    decodeStack (z,o,bits.map (fun b => if b then o else z)) = some bits := by
  have hv : ∀ b : Bool, validSymbol z o (if b then o else z) = true := by
    intro b; cases b <;> simp [validSymbol]
  have hd : ∀ b : Bool, decodedBit o (if b then o else z) = b := by
    intro b
    cases b with
    | false => simp [decodedBit,hne]
    | true => simp [decodedBit]
  simp [decodeStack,hne,List.all_map,List.map_map,Function.comp_def,hv,hd]

/-- Decode only a halted numeric result; no other-stack cleanup is asserted by
this operation. -/
def extractMemory (p : Nat × Nat × Nat × Option Nat × Stacks) : Option (List Bool) :=
  if p.2.2.2.1.isSome then none
  else if p.2.2.1 < p.2.2.2.2.length then
    decodeStack (p.1,p.2.1,stackFn p.2.2.2.2 p.2.2.1)
  else none

set_option maxHeartbeats 1000000 in
theorem extractMemory_primrec : Primrec extractMemory := by
  let A := Nat × Nat × Nat × Option Nat × Stacks
  have hz : Primrec (fun p : A => p.1) := Primrec.fst
  have ho : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun p : A => p.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hm : Primrec (fun p : A => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hstk : Primrec (fun p : A => stackFn p.2.2.2.2 p.2.2.1) := stackFn_primrec.comp hm hi
  have hdec : Primrec (fun p : A => decodeStack (p.1,p.2.1,stackFn p.2.2.2.2 p.2.2.1)) :=
    decodeStack_primrec.comp (Primrec.pair hz (Primrec.pair ho hstk))
  have hlen : Primrec (fun p : A => p.2.2.2.2.length) := Primrec.list_length.comp hm
  have hinside : Primrec (fun p : A => if p.2.2.1 < p.2.2.2.2.length then
      decodeStack (p.1,p.2.1,stackFn p.2.2.2.2 p.2.2.1) else none) :=
    Primrec.ite (Primrec.nat_lt.comp hi hlen) hdec (Primrec.const none)
  apply (Primrec.cond (Primrec.option_isSome.comp hl) (Primrec.const none) hinside).of_eq
  intro p
  cases h : p.2.2.2.1 <;> simp [extractMemory,h]

theorem extractMemory_computable : Computable extractMemory := extractMemory_primrec.to_comp

/-- A configuration related to a canonical library halt retains the entire
encoded output, in order, including the empty list. -/
theorem related_halt_extracts {αΓ : Type} (aux : Turing.TM2ComputableAux αΓ Bool)
    (N : Numbering aux.tm.Γ aux.tm.Λ aux.tm.σ) (r : Result) (bits : List Bool)
    (hr : CfgRel N (Turing.haltList aux.tm (bits.map aux.outputAlphabet.symm)) (erase r))
    (hvalid : r.memory.length = N.stackCount) :
    extractMemory (outputSymbol aux N false,outputSymbol aux N true,
      (N.stack aux.tm.k₁).val,r.label,r.memory) = some bits := by
  have hl : r.label = none := by simpa [CfgRel,erase,Turing.haltList] using hr.1
  have hs := hr.2.2 aux.tm.k₁
  change stackFn r.memory (N.stack aux.tm.k₁).val =
    ((Turing.haltList aux.tm (bits.map aux.outputAlphabet.symm)).stk aux.tm.k₁).map
      (fun x => (N.symbol aux.tm.k₁ x).val) at hs
  rw [Shared.ComplexityBridge.TM2Symbols.haltList_output] at hs
  have hstack : stackFn r.memory (N.stack aux.tm.k₁).val =
      bits.map (fun b => if b then outputSymbol aux N true else outputSymbol aux N false) := by
    rw [hs,List.map_map]
    apply List.map_congr_left
    intro b _
    cases b <;> rfl
  have hindex : (N.stack aux.tm.k₁).val < r.memory.length := by
    rw [hvalid]
    exact (N.stack aux.tm.k₁).isLt
  simp only [extractMemory,hl,Option.isSome_none,Bool.false_eq_true,if_false,hindex,if_true,hstack]
  exact decodeStack_encoded _ _ (outputSymbols_ne aux N) bits

/-- Every canonical polynomial-time function has one finite numeric program
with a computable initializer and extractor for its entire encoded output.
The same whole-block clock applies for every input. -/
theorem canonicalPoly_numeric_io {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (hf : ComplexityTheory.IsPolyTime f) :
    ∃ (h : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := α))
        (BitstringEncoding.bitEncode (α := β)) f)
      (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Shared.Codes.TM2Statements.Code)
      (e : Nat) (d : InputData) (z o out : Nat),
      decodeProgram e = some p ∧ d = inputData h.toTM2ComputableAux N ∧ validInputData d = true ∧
      programValid p N.stackCount N.states N.symbols = true ∧
      z = outputSymbol h.toTM2ComputableAux N false ∧
      o = outputSymbol h.toTM2ComputableAux N true ∧ out = (N.stack h.tm.k₁).val ∧
      ∀ a, ∃ start r, buildStart d (BitstringEncoding.bitEncode a) = some start ∧
        run p (h.time.eval (BitstringEncoding.bitEncode a).length) start = .halted r ∧
        CfgRel N (Turing.haltList h.tm
          ((BitstringEncoding.bitEncode (f a)).map h.outputAlphabet.invFun)) (erase r) ∧
        extractMemory (z,o,out,r.label,r.memory) = some (BitstringEncoding.bitEncode (f a)) := by
  obtain ⟨h,N,p,e,he,hp,hv,hr⟩ := canonicalPoly_numeric f hf
  let d := inputData h.toTM2ComputableAux N
  let z := outputSymbol h.toTM2ComputableAux N false
  let o := outputSymbol h.toTM2ComputableAux N true
  let out := (N.stack h.tm.k₁).val
  refine ⟨h,N,p,e,d,z,o,out,he,rfl,inputData_valid h.toTM2ComputableAux N,hv,rfl,rfl,rfl,?_⟩
  intro a
  obtain ⟨r,hrun,hrel⟩ := hr a
  refine ⟨encodeConfig N (Turing.initList h.tm
    ((BitstringEncoding.bitEncode a).map h.inputAlphabet.invFun)),r,?_,hrun,hrel,?_⟩
  · exact buildStart_eq h.toTM2ComputableAux N (BitstringEncoding.bitEncode a)
  · have hstart := encodeConfig_valid N h.tm.m (Turing.initList h.tm
        ((BitstringEncoding.bitEncode a).map h.inputAlphabet.invFun))
    rw [← hp] at hstart
    have hsafe := run_safe p N.stackCount N.states N.symbols hv
      (h.time.eval (BitstringEncoding.bitEncode a).length) _ hstart
    rw [hrun] at hsafe
    have hmemory : r.memory.length = N.stackCount := hsafe.1.2.1.1
    exact related_halt_extracts h.toTM2ComputableAux N r (BitstringEncoding.bitEncode (f a)) hrel hmemory

namespace Evaluator
open Shared.Codes.TM2Candidate (Candidate)
open Shared.Codes.TM2CheckedCandidate (candidateValid candidateValid_primrec)
open Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability

/-- Check output symbol and stack indices against the same finite descriptor
used to validate the program. Input validation remains in `buildRaw`. -/
def descriptorValid (c : Candidate) : Bool :=
  candidateValid c && decide (c.2.1 < c.1.2.2.1.2.2) &&
    decide (c.2.2.1 < c.1.2.2.1.2.2) && (c.2.1 != c.2.2.1) &&
    decide (c.2.2.2 < c.1.2.2.1.1)

theorem descriptorValid_primrec : Primrec descriptorValid := by
  have hp : Primrec (fun c : Candidate => candidateValid c) := candidateValid_primrec
  have hz : Primrec (fun c : Candidate => c.2.1) := Primrec.fst.comp Primrec.snd
  have ho : Primrec (fun c : Candidate => c.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hout : Primrec (fun c : Candidate => c.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hdata : Primrec (fun c : Candidate => c.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hsymbols : Primrec (fun c : Candidate => c.1.2.2.1.2.2) :=
    (Primrec.snd.comp Primrec.snd).comp hdata
  have hstacks : Primrec (fun c : Candidate => c.1.2.2.1.1) := Primrec.fst.comp hdata
  have h1 := (Primrec.nat_lt.comp hz hsymbols).decide
  have h2 := (Primrec.nat_lt.comp ho hsymbols).decide
  have h3 := Primrec.not.comp (Primrec.beq.comp hz ho)
  have h4 := (Primrec.nat_lt.comp hout hstacks).decide
  have h := Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp hp h1) h2) h3) h4
  apply h.of_eq
  intro c
  simp [descriptorValid,bne]

/-- An executable checked runner over already-encoded input bits. The fixed
exponent clocks TM2 statement blocks; failure, timeout and malformed output
all return `none`. -/
def evaluate (c : Candidate) (bits : List Bool) : Option (List Bool) :=
  if descriptorValid c then do
    let start ← buildRaw (c.1.2.2,bits)
    let (halted,r) ← runEncoded ((c.1.1,(bits.length+2)^c.1.2.1),start)
    if halted then extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.1,r.2.2) else none
  else none

def output (p : Candidate × (Bool × ResultRaw)) : Option (List Bool) :=
  if p.2.1 then extractMemory (p.1.2.1,p.1.2.2.1,p.1.2.2.2,p.2.2.1,p.2.2.2.2) else none

theorem output_primrec : Primrec output := by
  let P := Candidate × (Bool × ResultRaw)
  have hz : Primrec (fun p : P => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ho : Primrec (fun p : P => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hout : Primrec (fun p : P => p.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hr : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun p : P => p.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hx : Primrec (fun p : P => extractMemory (p.1.2.1,p.1.2.2.1,p.1.2.2.2,p.2.2.1,p.2.2.2.2)) :=
    extractMemory_primrec.comp (Primrec.pair hz (Primrec.pair ho (Primrec.pair hout (Primrec.pair hr hm))))
  have h := Primrec.cond (Primrec.fst.comp (Primrec.snd : Primrec (fun p : P => p.2))) hx (Primrec.const none)
  apply h.of_eq
  rintro ⟨c,b,r⟩
  cases b <;> rfl

set_option maxHeartbeats 1000000 in
theorem evaluate_primrec : Primrec₂ evaluate := by
  let P := Candidate × List Bool
  have hi : Primrec (fun p : P => buildRaw (p.1.1.2.2,p.2)) :=
    buildRaw_primrec.comp (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
  have hc : Primrec (fun p : P × ResultRaw => (p.1.2.length+2)^p.1.1.1.2.1) :=
    Shared.Codes.FinitePrograms.clock_primrec.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hr : Primrec (fun p : P × ResultRaw => runEncoded ((p.1.1.1.1,(p.1.2.length+2)^p.1.1.1.2.1),p.2)) :=
    runEncoded_primrec.comp (Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) hc) Primrec.snd)
  have ho : Primrec₂ (fun (p : P × ResultRaw) (r : Bool × ResultRaw) => output (p.1.1,r)) :=
    (output_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂
  have heval := Primrec.option_bind hi (Primrec.option_bind hr ho).to₂
  have hvalid : Primrec (fun p : P => descriptorValid p.1) := descriptorValid_primrec.comp Primrec.fst
  have h := Primrec.cond hvalid heval (Primrec.const none)
  apply h.to₂.of_eq
  intro c bits
  unfold evaluate output
  cases hv : descriptorValid c with
  | false => simp
  | true =>
    simp only [↓reduceIte]
    cases hs : buildRaw (c.1.2.2,bits) with
    | none => rfl
    | some start =>
      simp only [Option.bind_some]
      cases hr : runEncoded ((c.1.1,(bits.length+2)^c.1.2.1),start) with
      | none => simp [hr]
      | some p => rcases p with ⟨b,r⟩; cases b <;> simp [hr]

theorem evaluate_computable : Computable₂ evaluate := evaluate_primrec.to_comp

theorem invalid_rejected (c : Candidate) (bits : List Bool) (h : descriptorValid c = false) :
    evaluate c bits = none := by simp [evaluate,h]

theorem invalid_input_rejected (c : Candidate) (bits : List Bool)
    (h : buildRaw (c.1.2.2,bits) = none) : evaluate c bits = none := by
  unfold evaluate
  split <;> simp [h]

theorem timeout_rejected (c : Candidate) (bits : List Bool) (start r : ResultRaw)
    (hvalid : descriptorValid c = true) (hs : buildRaw (c.1.2.2,bits) = some start)
    (hr : runEncoded ((c.1.1,(bits.length+2)^c.1.2.1),start) = some (false,r)) :
    evaluate c bits = none := by simp [evaluate,hvalid,hs,hr]

theorem malformed_output_rejected (c : Candidate) (bits : List Bool) (start r : ResultRaw)
    (hvalid : descriptorValid c = true) (hs : buildRaw (c.1.2.2,bits) = some start)
    (hr : runEncoded ((c.1.1,(bits.length+2)^c.1.2.1),start) = some (true,r))
    (ho : extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.1,r.2.2) = none) :
    evaluate c bits = none := by simp [evaluate,hvalid,hs,hr,ho]

/-- Coverage is uniform in the input, including the empty bitstring. It is
forward coverage in block-clock semantics, not a polynomial bit-cost bound. -/
theorem canonicalPoly_covers {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (hf : ComplexityTheory.IsPolyTime f) :
    ∃ c : Candidate, descriptorValid c = true ∧ ∀ a,
      evaluate c (BitstringEncoding.bitEncode a) = some (BitstringEncoding.bitEncode (f a)) := by
  obtain ⟨h,N,p,e,d,z,o,out,he,hdata,hd,hv,hz,ho,hout,hr⟩ := canonicalPoly_numeric_io f hf
  obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent h.time
  let c : Candidate := ((e,k,inputRaw d),(z,o,out))
  have hzbound : z < N.symbols := by
    rw [hz,outputSymbol]
    exact Nat.lt_of_lt_of_le (N.symbol h.tm.k₁ (h.outputAlphabet.symm false)).isLt (N.symbol_bound h.tm.k₁)
  have hobound : o < N.symbols := by
    rw [ho,outputSymbol]
    exact Nat.lt_of_lt_of_le (N.symbol h.tm.k₁ (h.outputAlphabet.symm true)).isLt (N.symbol_bound h.tm.k₁)
  have hne : z ≠ o := by rw [hz,ho]; exact outputSymbols_ne h.toTM2ComputableAux N
  have hvalid : descriptorValid c = true := by
    simp [descriptorValid,c,candidateValid,he,inputRaw,hdata,inputData,hv,hzbound,hobound,hne,hout]
  refine ⟨c,hvalid,?_⟩
  intro a
  obtain ⟨start,r,hstart,hrun,hrel,houtput⟩ := hr a
  have hinit : buildRaw (inputRaw d,BitstringEncoding.bitEncode a) = some (resultRaw start) := by
    rw [buildRaw_eq,hstart]
    rfl
  have hrun' : run p (((BitstringEncoding.bitEncode a).length+2)^k) start = .halted r :=
    run_halted_mono p start r (hk (BitstringEncoding.bitEncode a).length) hrun
  have heval : runEncoded ((e,((BitstringEncoding.bitEncode a).length+2)^k),resultRaw start) =
      some (true,resultRaw r) := by
    have heval' := runEncoded_of_decode e p (((BitstringEncoding.bitEncode a).length+2)^k) start he
    rw [hrun'] at heval'
    exact heval'
  unfold evaluate
  rw [hvalid]
  simp only [↓reduceIte]
  change (buildRaw (inputRaw d,BitstringEncoding.bitEncode a)).bind (fun start' =>
    (runEncoded ((e,((BitstringEncoding.bitEncode a).length+2)^k),start')).bind fun (v : Bool × ResultRaw) =>
      if v.1 then extractMemory (z,o,out,v.2.1,v.2.2.2) else none) = _
  rw [hinit]
  change (runEncoded ((e,((BitstringEncoding.bitEncode a).length+2)^k),resultRaw start)).bind _ = _
  rw [heval]
  simpa [resultRaw] using houtput

end Evaluator

namespace Fixtures
open Shared.Codes.TM2Micro
example : decodeStack (0,1,[]) = some [] := by decide
example : decodeStack (0,1,[1,0,1]) = some [true,false,true] := by decide
example : decodeStack (0,1,[0,2]) = none := by decide
example : decodeStack (0,0,[]) = none := by decide
example : extractMemory (0,1,0,none,[[1,0]]) = some [true,false] := by decide
example : extractMemory (0,1,0,some 0,[[1,0]]) = none := by decide
example : extractMemory (0,1,1,none,[[]]) = none := by decide

def emptyOutputCandidate : Shared.Codes.TM2Candidate.Candidate :=
  ((Encodable.encode ([Shared.Codes.TM2Statements.Code.halt] : List Shared.Codes.TM2Statements.Code),0,
      inputRaw ⟨2,1,2,1,0,0,0,0,1⟩),(0,1,1))

theorem emptyOutputCandidate_valid : Evaluator.descriptorValid emptyOutputCandidate = true := by
  have he := decodeProgram_coverage ([Shared.Codes.TM2Statements.Code.halt] : List Shared.Codes.TM2Statements.Code)
  change decodeProgram (Nat.pair (Encodable.encode Shared.Codes.TM2Statements.Code.halt) 0 + 1) =
    some [Shared.Codes.TM2Statements.Code.halt] at he
  simp [Evaluator.descriptorValid,Shared.Codes.TM2CheckedCandidate.candidateValid,
    emptyOutputCandidate,he,inputRaw,programValid,Shared.Codes.TM2StatementValidation.valid]

theorem emptyOutputCandidate_evaluates_empty : Evaluator.evaluate emptyOutputCandidate [] = some [] := by
  let start : Result := ⟨some 0,0,[[],[]]⟩
  have hs : buildRaw (inputRaw ⟨2,1,2,1,0,0,0,0,1⟩,[]) = some (resultRaw start) := by decide
  have hr := Shared.Codes.TM2Micro.runEncoded_correct
    ([Shared.Codes.TM2Statements.Code.halt] : List Shared.Codes.TM2Statements.Code) 1 start
  have hr' : runEncoded ((Encodable.encode ([Shared.Codes.TM2Statements.Code.halt] :
      List Shared.Codes.TM2Statements.Code),1),resultRaw start) = some (true,(none,0,[[],[]])) := by
    simpa [start,run,Shared.Codes.TM2FixedComputability.outcomeRaw,resultRaw,
      Shared.Codes.TM2StatementExecution.exec] using hr
  unfold Evaluator.evaluate
  rw [emptyOutputCandidate_valid]
  simp only [↓reduceIte]
  change (buildRaw (inputRaw ⟨2,1,2,1,0,0,0,0,1⟩,[])).bind (fun s =>
    (runEncoded ((Encodable.encode ([Shared.Codes.TM2Statements.Code.halt] :
      List Shared.Codes.TM2Statements.Code),1),s)).bind fun (v : Bool × ResultRaw) =>
      if v.1 then extractMemory (0,1,1,v.2.1,v.2.2.2) else none) = _
  rw [hs]
  change (runEncoded ((Encodable.encode ([Shared.Codes.TM2Statements.Code.halt] :
    List Shared.Codes.TM2Statements.Code),1),resultRaw start)).bind _ = _
  rw [hr']
  rfl

example : Evaluator.descriptorValid
    ((Encodable.encode ([Shared.Codes.TM2Statements.Code.halt] : List Shared.Codes.TM2Statements.Code),0,
      inputRaw ⟨2,1,2,1,0,0,0,0,1⟩),(0,0,1)) = false := by
  simp [Evaluator.descriptorValid]
end Fixtures
end Shared.ComplexityBridge.TM2BitstringOutput
