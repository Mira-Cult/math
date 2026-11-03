import Shared.Codes.TM2Micro
import Shared.ComplexityBridge.TM2RawInput

set_option maxHeartbeats 600000

/-! Uniform, total clocked Boolean evaluation of numeric TM2 candidates.
The source gives forward coverage of the pinned canonical P class. It does not
prove that every accepted numeric table is globally valid or that whole-block
clocks imply polynomial bit costs; no class-equality characterization follows. -/
namespace Shared.Codes.TM2Candidate
open Shared.Codes.TM2Micro Shared.Codes.TM2Program Shared.Codes.TM2FixedComputability
open Shared.Codes.TM2StatementExecution Shared.ComplexityBridge.TM2BooleanInput
open Shared.ComplexityBridge.TM2RawInput Shared.ComplexityBridge.TM2BooleanOutput

/-- Numeric program code, fixed clock exponent, initialization parameters,
and three Boolean output parameters. -/
abbrev Candidate := (Nat × Nat × InputRaw) × (Nat × Nat × Nat)

/-- Initialization or execution failure, timeout, or malformed Boolean
output returns `none`. The clock counts whole TM2 statement blocks. -/
def evaluate (c : Candidate) (input : List Bool) : Option Bool := do
  let start ← buildDecisionInput (c.1.2.2,input)
  let (halted,r) ← runEncoded ((c.1.1,(input.length+2)^c.1.2.1),start)
  if halted then extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.1,r.2.2) else none

def output (p : Candidate × (Bool × ResultRaw)) : Option Bool :=
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

theorem evaluate_primrec : Primrec₂ evaluate := by
  let P := Candidate × List Bool
  have hi : Primrec (fun p : P => buildDecisionInput (p.1.1.2.2,p.2)) :=
    buildDecisionInput_primrec.comp (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
  have hc : Primrec (fun p : P × ResultRaw => (p.1.2.length+2)^p.1.1.1.2.1) :=
    Shared.Codes.FinitePrograms.clock_primrec.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hr : Primrec (fun p : P × ResultRaw => runEncoded ((p.1.1.1.1,(p.1.2.length+2)^p.1.1.1.2.1),p.2)) :=
    runEncoded_primrec.comp (Primrec.pair (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) hc) Primrec.snd)
  have ho : Primrec₂ (fun (p : P × ResultRaw) (r : Bool × ResultRaw) => output (p.1.1,r)) :=
    (output_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂
  have h := Primrec.option_bind hi (Primrec.option_bind hr ho).to₂
  apply h.to₂.of_eq
  intro c input
  unfold evaluate output
  cases hs : buildDecisionInput (c.1.2.2,input) with
  | none => rfl
  | some start =>
    simp only [Option.bind_some]
    cases hr : runEncoded ((c.1.1,(input.length+2)^c.1.2.1),start) with
    | none => simp [hr]
    | some p => rcases p with ⟨b,r⟩; cases b <;> simp [hr]

theorem evaluate_computable : Computable₂ evaluate := evaluate_primrec.to_comp

theorem evaluate_invalid (c : Candidate) (input : List Bool) (h : decodeProgram c.1.1 = none) :
    evaluate c input = none := by
  unfold evaluate
  cases hs : buildDecisionInput (c.1.2.2,input) with
  | none => simp
  | some start =>
    simp [runEncoded_invalid c.1.1 ((input.length+2)^c.1.2.1) start h]

theorem evaluate_timeout (c : Candidate) (input : List Bool) (start r : ResultRaw)
    (hs : buildDecisionInput (c.1.2.2,input) = some start)
    (hr : runEncoded ((c.1.1,(input.length+2)^c.1.2.1),start) = some (false,r)) :
    evaluate c input = none := by
  unfold evaluate
  simp [hs, hr]


/-- Forward coverage only: every canonical P language has one fixed numeric
program, clock exponent and input/output parameter tuple. -/
theorem canonicalP_covers (L : ComplexityTheory.DecisionProblem) (hL : L ∈ ComplexityTheory.P) :
    ∃ c : Candidate, ∀ x, evaluate c x = some (L x) := by
  obtain ⟨h,N,p,e,d,z,o,out,k,he,hd,hv,hr⟩ := canonicalP_rawInput L hL
  refine ⟨((e,k,d),(z,o,out)), ?_⟩
  intro x
  obtain ⟨start,r,hs,hrun,hrel,hout⟩ := hr x
  have heval : runEncoded ((e,(x.length+2)^k),resultRaw start) = some (true,resultRaw r) := by
    simpa [hrun, outcomeRaw] using runEncoded_of_decode e p ((x.length+2)^k) start he
  change (buildDecisionInput (d,x)).bind (fun start' =>
    (runEncoded ((e,(x.length+2)^k),start')).bind fun (v : Bool × ResultRaw) =>
      if v.1 then extractMemory (z,o,out,v.2.1,v.2.2.2) else none) = some (L x)
  rw [hs]
  change (runEncoded ((e,(x.length+2)^k),resultRaw start)).bind _ = some (L x)
  rw [heval]
  simpa [resultRaw] using hout

def decode (e : Nat) : Option Candidate := Encodable.decode e

theorem decode_primrec : Primrec decode := Primrec.decode

theorem decode_coverage (c : Candidate) : decode (Encodable.encode c) = some c := Encodable.encodek c


example : output (((0,0,((1,1,2),(1,0,0),(0,0,1))),(0,1,0)),
    (true,(none,0,[[0]]))) = some false := by decide
example : output (((0,0,((1,1,2),(1,0,0),(0,0,1))),(0,1,0)),
    (false,(some 0,0,[[0]]))) = none := by decide
example : output (((0,0,((1,1,2),(1,0,0),(0,0,1))),(0,1,0)),
    (true,(none,0,[[0,1]]))) = none := by decide

end Shared.Codes.TM2Candidate
