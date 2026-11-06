import Shared.Codes.TM2CheckedCandidate
/-! Uniform checked evaluation of raw input/witness pairs using the pinned
pair encoding. The clock exponent is fixed per candidate; its base is the sum
of the raw lengths plus two. The coverage theorem is one-way and counts whole
TM2 statement blocks, not bit operations. -/
namespace Shared.Codes.TM2PairCandidate
open Shared.Codes.TM2Candidate Shared.Codes.TM2CheckedCandidate Shared.Codes.TM2Program
open Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability Shared.Codes.TM2StatementExecution
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2RawInput
open Shared.ComplexityBridge.TM2BooleanOutput

/-- The pair checker uses the library encoding, but its explicit clock uses
raw input length plus raw witness length. -/
def evaluate (c : Candidate) (input witness : List Bool) : Option Bool := do
  if !candidateValid c then none else do
    let start ← buildPairInput (c.1.2.2,(input,witness))
    let (halted,r) ← runEncoded ((c.1.1,(input.length+witness.length+2)^c.1.2.1),start)
    if halted then extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.1,r.2.2) else none

theorem evaluate_primrec : Primrec (fun p : (Candidate × List Bool) × List Bool =>
    evaluate p.1.1 p.1.2 p.2) := by
  let A := (Candidate × List Bool) × List Bool
  have hc : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : A => p.2) := Primrec.snd
  have hv : Primrec (fun p : A => candidateValid p.1.1) := candidateValid_primrec.comp hc
  have hd : Primrec (fun p : A => p.1.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hc))
  have hi : Primrec (fun p : A => buildPairInput (p.1.1.1.2.2,(p.1.2,p.2))) :=
    buildPairInput_primrec.comp (Primrec.pair hd (Primrec.pair hx hw))
  have hexp : Primrec (fun p : A => p.1.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp hc))
  have hcode : Primrec (fun p : A => p.1.1.1.1) := Primrec.fst.comp (Primrec.fst.comp hc)
  have hlen : Primrec (fun p : A => p.1.2.length+p.2.length+2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.list_length.comp hx) (Primrec.list_length.comp hw)) (Primrec.const 2)
  have hpow : Primrec (fun p : A => (p.1.2.length+p.2.length+2)^p.1.1.1.2.1) :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp hlen hexp
  have hr : Primrec (fun p : A × ResultRaw =>
      runEncoded ((p.1.1.1.1.1,(p.1.1.2.length+p.1.2.length+2)^p.1.1.1.1.2.1),p.2)) := by
    have h := runEncoded_primrec.comp (Primrec.pair (Primrec.pair (hcode.comp Primrec.fst) (hpow.comp Primrec.fst)) Primrec.snd)
    exact h.of_eq (by intro p; rfl)
  have ho : Primrec₂ (fun (p : A × ResultRaw) (r : Bool × ResultRaw) =>
      output (p.1.1.1,r)) :=
    (output_primrec.comp (Primrec.pair (hc.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂
  have hrun := Primrec.option_bind hi (Primrec.option_bind hr ho).to₂
  have h := Primrec.cond hv hrun (Primrec.const none)
  apply h.of_eq
  rintro ⟨⟨c,x⟩,w⟩
  unfold evaluate output
  cases hc : candidateValid c with
  | false => simp
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hs : buildPairInput (c.1.2.2,(x,w)) with
    | none => simp
    | some start =>
      cases hr : runEncoded ((c.1.1,(x.length+w.length+2)^c.1.2.1),start) with
      | none => simp [hr]
      | some p => rcases p with ⟨b,r⟩; cases b <;> simp [hr]

theorem evaluate_computable : Computable (fun p : (Candidate × List Bool) × List Bool =>
    evaluate p.1.1 p.1.2 p.2) := evaluate_primrec.to_comp

theorem invalid_rejected (c : Candidate) (x w : List Bool) (h : candidateValid c = false) :
    evaluate c x w = none := by simp [evaluate, h]

/-- Absorb the actual pair encoding length into a raw-pair fixed exponent. -/
theorem pairClock_bound (x w : List Bool) (k : Nat) :
    ((BitstringEncoding.bitEncode (x,w)).length+2)^k ≤ (x.length+w.length+2)^(4*k) := by
  let n := x.length+w.length
  have hbase : 6*n+3 ≤ (n+2)^4 := by
    have h₁ : 6*n+3 ≤ 8*(n+2) := by omega
    have h₂ : 8 ≤ (n+2)^3 := by
      calc
        8 = 2^3 := by decide
        _ ≤ (n+2)^3 := Nat.pow_le_pow_left (by omega) 3
    calc
      6*n+3 ≤ 8*(n+2) := h₁
      _ ≤ (n+2)^3*(n+2) := Nat.mul_le_mul_right (n+2) h₂
      _ = (n+2)^4 := (pow_succ (n+2) 3).symm
  have hsize : (BitstringEncoding.bitEncode (x,w)).length+2 ≤ (n+2)^4 := by
    rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
    exact le_trans (by dsimp [n]; omega) hbase
  calc
    ((BitstringEncoding.bitEncode (x,w)).length+2)^k ≤ ((n+2)^4)^k := Nat.pow_le_pow_left hsize k
    _ = (x.length+w.length+2)^(4*k) := by simp [n, pow_mul]

/-- Every canonical polynomial-time Boolean relation has one globally
validated candidate which works for every raw input/witness pair. -/
theorem canonicalPoly_covers (R : (List Bool × List Bool) → Bool) (hR : ComplexityTheory.IsPolyTime R) :
    ∃ c : Candidate, candidateValid c = true ∧ ∀ x w, evaluate c x w = some (R (x,w)) := by
  obtain ⟨h,N,p,e,d,he,hd,hv,hr⟩ := canonicalPoly_boolean_io R hR
  obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent h.time
  let z := outputSymbol h.toTM2ComputableAux N false
  let o := outputSymbol h.toTM2ComputableAux N true
  let out := (N.stack h.tm.k₁).val
  let c : Candidate := ((e,4*k,inputRaw d),(z,o,out))
  have hvalid : candidateValid c = true := by
    simp [candidateValid, c, he, inputRaw, hd, inputData, hv]
  refine ⟨c,hvalid,?_⟩
  intro x w
  obtain ⟨start,r,hstart,hrun,hrel,hout⟩ := hr (x,w)
  have hinit : buildPairInput (inputRaw d,(x,w)) = some (resultRaw start) := by
    simp [buildPairInput, buildRaw_eq, hstart]
  have hclock : h.time.eval (BitstringEncoding.bitEncode (x,w)).length ≤
      (x.length+w.length+2)^(4*k) := le_trans (hk _) (pairClock_bound x w k)
  have hrun' : run p ((x.length+w.length+2)^(4*k)) start = .halted r :=
    run_halted_mono p start r hclock hrun
  have heval : runEncoded ((e,(x.length+w.length+2)^(4*k)),resultRaw start) = some (true,resultRaw r) := by
    simpa [hrun', outcomeRaw] using runEncoded_of_decode e p ((x.length+w.length+2)^(4*k)) start he
  unfold evaluate
  rw [hvalid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  change (buildPairInput (inputRaw d,(x,w))).bind (fun start' =>
    (runEncoded ((e,(x.length+w.length+2)^(4*k)),start')).bind fun (v : Bool × ResultRaw) =>
      if v.1 then extractMemory (z,o,out,v.2.1,v.2.2.2) else none) = some (R (x,w))
  rw [hinit]
  change (runEncoded ((e,(x.length+w.length+2)^(4*k)),resultRaw start)).bind _ = some (R (x,w))
  rw [heval]
  simpa [resultRaw,z,o,out] using hout

end Shared.Codes.TM2PairCandidate
