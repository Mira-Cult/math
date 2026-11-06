import Shared.NPCONP.TM2Verifier
import Shared.ComplexityBridge.TM2Whole
import Shared.Codes.TM2PairCandidate

namespace Shared.ComplexityBridge.TM2WholePair
open Shared.ComplexityBridge.TM2Whole Shared.ComplexityBridge.TM2BooleanInput
open Shared.ComplexityBridge.TM2FiniteBoundary Shared.ComplexityBridge.TM2BooleanOutput
open Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2StackBound
open Shared.Codes.TM2Program Shared.Codes.TM2Candidate Shared.Codes.TM2CheckedCandidate
open Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability Shared.Codes.TM2StatementExecution

/-- Successful pair evaluation implies validated initialization, a main label
inside the actual program, and a genuine halted numeric result. -/
theorem pair_numeric_result (c : Candidate) (p : Program) (hdecode : decodeProgram c.1.1 = some p)
    (x w : List Bool) (b : Bool) (heval : Shared.Codes.TM2PairCandidate.evaluate c x w = some b) :
    let d := inputDataOfRaw c.1.2.2
    validInputData d = true ∧ d.main < p.length ∧ programValid p d.stackCount d.states d.symbols = true ∧
    ∃ start r, buildStart d (BitstringEncoding.bitEncode (x,w)) = some start ∧
      run p ((x.length+w.length+2)^c.1.2.1) start = .halted r ∧
      extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.label,r.memory) = some b := by
  let d := inputDataOfRaw c.1.2.2
  have hcandidate : candidateValid c = true := by
    cases hv : candidateValid c with
    | false => simp [Shared.Codes.TM2PairCandidate.evaluate, hv] at heval
    | true => rfl
  have hp : programValid p d.stackCount d.states d.symbols = true := by
    have hv := hcandidate
    simp [candidateValid, hdecode] at hv
    exact hv
  have hdata : validInputData d = true := by
    cases hd : validInputData d with
    | true => rfl
    | false =>
      have hin : Shared.ComplexityBridge.TM2RawInput.buildPairInput (c.1.2.2,(x,w)) = none := by
        change buildRaw (c.1.2.2,BitstringEncoding.bitEncode (x,w)) = none
        have heq : c.1.2.2 = inputRaw d := by simp [d]
        rw [heq,buildRaw_eq]
        simp [buildStart,hd]
      unfold Shared.Codes.TM2PairCandidate.evaluate at heval
      simp [hcandidate,hin] at heval
  let start : Result := ⟨some d.main,d.initialState,
    (List.replicate d.stackCount []).set d.inputStack
      ((BitstringEncoding.bitEncode (x,w)).map (inputBit d.falseSymbol d.trueSymbol))⟩
  have hstart : buildStart d (BitstringEncoding.bitEncode (x,w)) = some start := by
    simp [buildStart,hdata,start]
  have hin : Shared.ComplexityBridge.TM2RawInput.buildPairInput (c.1.2.2,(x,w)) = some (resultRaw start) := by
    change buildRaw (c.1.2.2,BitstringEncoding.bitEncode (x,w)) = _
    have heq : c.1.2.2 = inputRaw d := by simp [d]
    rw [heq,buildRaw_eq,hstart]
    rfl
  have hrun := runEncoded_of_decode c.1.1 p ((x.length+w.length+2)^c.1.2.1) start hdecode
  unfold Shared.Codes.TM2PairCandidate.evaluate at heval
  simp only [hcandidate, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval
  rw [hin] at heval
  change (runEncoded ((c.1.1,(x.length+w.length+2)^c.1.2.1),resultRaw start)).bind (fun v =>
    if v.1 then extractMemory (c.2.1,c.2.2.1,c.2.2.2,v.2.1,v.2.2.2) else none) = some b at heval
  rw [hrun] at heval
  cases hr : run p ((x.length+w.length+2)^c.1.2.1) start with
  | invalid => simp [hr,outcomeRaw] at heval
  | timeout r => simp [hr,outcomeRaw] at heval
  | halted r =>
    have hout : extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.label,r.memory) = some b := by
      simpa [hr,outcomeRaw,resultRaw] using heval
    have hmain : d.main < p.length := by
      by_contra hh
      have hn : p[d.main]? = none := by apply List.getElem?_eq_none; omega
      cases hf : (x.length+w.length+2)^c.1.2.1 with
      | zero => simp [hf,run,start] at hr
      | succ n => simp [hf,run,start,hn] at hr
    exact ⟨hdata,hmain,hp,start,r,hstart,hr,hout⟩

/-- A successful pair evaluation runs through the whole Boolean TM2 with a
fixed polynomial bound measured in the actual encoded pair length. -/
theorem pair_whole_run (c : Candidate) (p : Program) (hdecode : decodeProgram c.1.1 = some p)
    (x w : List Bool) (b : Bool) (heval : Shared.Codes.TM2PairCandidate.evaluate c x w = some b) :
    let d := inputDataOfRaw c.1.2.2
    let tm := whole d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
      d.falseSymbol d.trueSymbol c.2.2.1
    ∃ t ≤ (timePolynomial d.stackCount c.1.2.1 p).eval (BitstringEncoding.bitEncode (x,w)).length,
      runSteps tm.step t (Turing.initList tm (BitstringEncoding.bitEncode (x,w))) = some (Turing.haltList tm [b]) := by
  let d := inputDataOfRaw c.1.2.2
  obtain ⟨hdata,hmain,hp,start,r,hstart,hrun,hout⟩ := pair_numeric_result c p hdecode x w b heval
  obtain ⟨t,ht,hr⟩ := numeric_run_complete d p c.2.2.2 c.2.1 c.2.2.1 (BitstringEncoding.bitEncode (x,w))
    ((x.length+w.length+2)^c.1.2.1) start r b hdata hmain hp hstart hrun hout
  let m := (BitstringEncoding.bitEncode (x,w)).length
  have hsize : x.length+w.length ≤ m := by
    dsimp [m]
    rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
    omega
  have hclock : (x.length+w.length+2)^c.1.2.1 ≤ (m+2)^c.1.2.1 := Nat.pow_le_pow_left (by omega) _
  have hprod := Nat.mul_le_mul_right (programDepth p) hclock
  have hinner : m + (x.length+w.length+2)^c.1.2.1 * programDepth p + 1 ≤
      m + (m+2)^c.1.2.1 * programDepth p + 1 := by omega
  have houter := Nat.mul_le_mul_left (d.stackCount+1) hinner
  refine ⟨t,?_,hr⟩
  rw [timePolynomial_eval]
  change t ≤ 1 + (2*m+2+(m+2)^c.1.2.1) +
    ((d.stackCount+1)*(m+(m+2)^c.1.2.1*programDepth p+1)+2)
  change t ≤ 1 + (2*m+2+(x.length+w.length+2)^c.1.2.1) +
    ((d.stackCount+1)*(m+(x.length+w.length+2)^c.1.2.1*programDepth p+1)+2) at ht
  omega

set_option backward.isDefEq.respectTransparency false in
/-- If one checked pair candidate succeeds on every input and witness, its
Boolean relation is polynomial-time in the canonical library definition. -/
theorem pair_total_isPolyTime (c : Candidate) (R : (List Bool × List Bool) → Bool)
    (h : ∀ x w, Shared.Codes.TM2PairCandidate.evaluate c x w = some (R (x,w))) :
    ComplexityTheory.IsPolyTime R := by
  have hcandidate : candidateValid c = true := by
    cases hv : candidateValid c with
    | false => have hh := h [] []; simp [Shared.Codes.TM2PairCandidate.evaluate,hv] at hh
    | true => rfl
  cases hdecode : decodeProgram c.1.1 with
  | none => simp [candidateValid,hdecode] at hcandidate
  | some p =>
    let d := inputDataOfRaw c.1.2.2
    let tm := wholeAux c p
    refine ⟨{ toTM2ComputableAux := tm, time := timePolynomial d.stackCount c.1.2.1 p, outputsFun := ?_ }⟩
    intro a
    let hrun := pair_whole_run c p hdecode a.1 a.2 (R a) (by cases a; exact h _ _)
    let n := Classical.choose hrun
    have hn := Classical.choose_spec hrun
    refine ⟨⟨n,?_⟩,hn.1⟩
    have hr := hn.2
    rw [runSteps_iterate] at hr
    change (fun o => o.bind tm.tm.step)^[n]
      (some (Turing.initList tm.tm ((BitstringEncoding.bitEncode a).map id))) =
        some (Turing.haltList tm.tm ([R a].map id))
    rw [List.map_id,List.map_id]
    exact hr

/-- Complete two-way characterization for globally total checked pair
candidates. This is not yet the bounded-witness verifier characterization. -/
theorem pair_candidate_iff_poly (R : (List Bool × List Bool) → Bool) :
    (∃ c : Candidate, ∀ x w, Shared.Codes.TM2PairCandidate.evaluate c x w = some (R (x,w))) ↔
      ComplexityTheory.IsPolyTime R := by
  constructor
  · rintro ⟨c,h⟩
    exact pair_total_isPolyTime c R h
  · intro h
    obtain ⟨c,_,hc⟩ := Shared.Codes.TM2PairCandidate.canonicalPoly_covers R h
    exact ⟨c,hc⟩

/-- This is the exact total Boolean relation accepted by a verifier: timeouts
are false and the verifier's original witness cutoff is preserved. -/
def verifierRelation (v : Shared.NPCONP.TM2Verifier.Verifier) (a : List Bool × List Bool) : Bool :=
  (Shared.NPCONP.TM2Verifier.verify v a.1 a.2).getD false

theorem verifierRelation_true_iff (v : Shared.NPCONP.TM2Verifier.Verifier) (x w : List Bool) :
    verifierRelation v (x,w) = true ↔ Shared.NPCONP.TM2Verifier.verify v x w = some true := by
  unfold verifierRelation
  cases Shared.NPCONP.TM2Verifier.verify v x w <;> simp

/-- A good bounded verifier proves canonical NP membership once its exact
cutoff-preserving Boolean relation is independently shown polynomial-time. -/
theorem good_verifier_in_NP_of_relation_poly (v : Shared.NPCONP.TM2Verifier.Verifier)
    (hgood : ∀ x, Shared.NPCONP.TM2Verifier.test v x = true)
    (hpoly : ComplexityTheory.IsPolyTime (verifierRelation v)) :
    Shared.ComplexityBridge.CNF.complementSat ∈ ComplexityTheory.NP := by
  refine ⟨(Polynomial.X + Polynomial.C 2)^v.1.1,verifierRelation v,hpoly,?_⟩
  intro x
  have htest := (Shared.NPCONP.TM2Verifier.test_iff v x).1 (hgood x)
  have haccept := htest.2.2
  change (Shared.ComplexityBridge.CNF.complementSat x = true) ↔
    ∃ w, w.length ≤ ((Polynomial.X + Polynomial.C 2)^v.1.1).eval x.length ∧ verifierRelation v (x,w) = true
  rw [← haccept]
  simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
    Shared.NPCONP.TM2Verifier.witnessBound,verifierRelation_true_iff]

/-- The precise remaining verifier wrapper obligation: every good verifier's
cutoff-preserving Boolean relation is polynomial-time in the canonical model. -/
def GoodVerifierRelationPoly : Prop :=
  ∀ v : Shared.NPCONP.TM2Verifier.Verifier,
    (∀ x, Shared.NPCONP.TM2Verifier.test v x = true) → ComplexityTheory.IsPolyTime (verifierRelation v)

/-- This conditional equivalence keeps the unresolved wrapper obligation
visible; the reverse coverage was already proved without it. -/
theorem good_verifier_iff_complement_in_NP (hpoly : GoodVerifierRelationPoly) :
    (∃ v : Shared.NPCONP.TM2Verifier.Verifier, ∀ x, Shared.NPCONP.TM2Verifier.test v x = true) ↔
      Shared.ComplexityBridge.CNF.complementSat ∈ ComplexityTheory.NP := by
  constructor
  · rintro ⟨v,hv⟩
    exact good_verifier_in_NP_of_relation_poly v hv (hpoly v hv)
  · exact Shared.NPCONP.TM2Verifier.complementSat_in_NP_covers

/-- Separate NP-versus-coNP conditional endpoint: it requires the exact
verifier wrapper, completeness, NP reduction closure, and a concrete
progress-sensitive comparison certificate. -/
theorem npconp_certified_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (np_pullback : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.NP)
    (hpoly : GoodVerifierRelationPoly) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP := by
  calc
    M.system.EventuallySilent ↔ ∃ v : Shared.NPCONP.TM2Verifier.Verifier, ∀ x, Shared.NPCONP.TM2Verifier.test v x = true :=
      Shared.NPCONP.TM2Verifier.certified_machine_silent_iff cert
    _ ↔ Shared.ComplexityBridge.CNF.complementSat ∈ ComplexityTheory.NP := good_verifier_iff_complement_in_NP hpoly
    _ ↔ ComplexityTheory.NP = ComplexityTheory.coNP := by
      rw [Shared.ComplexityBridge.CanonicalClasses.totalComplement_eq]
      exact (Shared.ComplexityBridge.CanonicalClasses.np_eq_conp_iff_complement_complete_in_np complete np_pullback).symm

end Shared.ComplexityBridge.TM2WholePair
