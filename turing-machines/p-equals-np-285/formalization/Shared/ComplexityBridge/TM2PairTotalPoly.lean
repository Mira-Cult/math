import Shared.ComplexityBridge.TM2PairTotalizer

namespace Shared.ComplexityBridge.TM2PairTotalPoly
open Shared.ComplexityBridge.TM2BooleanInput Shared.Codes.TM2Program
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation
open Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2StackBound
open Shared.Codes.TM2Candidate Shared.Codes.TM2CheckedCandidate Shared.Codes.TM2Micro
open Shared.Codes.TM2FixedComputability Shared.ComplexityBridge.TM2RawInput Shared.ComplexityBridge.TM2FiniteBoundary

/-- The total fixed-clock numeric checker: timeout, malformed initialization,
and malformed Boolean outputs yield false. -/
def boundedNumeric (d : InputData) (k : Nat) (p : Program) (output z one : Nat)
    (a : List Bool × List Bool) : Bool :=
  match buildStart d (BitstringEncoding.bitEncode a) with
  | none => false
  | some start =>
    match run p ((a.1.length+a.2.length+2)^k) start with
    | .halted r => (Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (z,one,output,r.label,r.memory)).getD false
    | _ => false

/-- One fixed polynomial in the actual encoded input length. -/
noncomputable def timePolynomial (ks k : Nat) (p : Program) : Polynomial Nat :=
  let x := Polynomial.X
  let clock := (x + Polynomial.C 2)^k
  let work := Polynomial.C (k*14)*(x + Polynomial.C 4)^k
  (Polynomial.C 4*x + Polynomial.C 10 + work + clock) +
    (Polynomial.C 5*(clock+(x+Polynomial.C 2)+Polynomial.C 1)+Polynomial.C 1 +
      Polynomial.C (ks+1)*(x+clock*Polynomial.C (programDepth p)+Polynomial.C 1)+Polynomial.C 3)

theorem timePolynomial_eval (ks k : Nat) (p : Program) (n : Nat) :
    (timePolynomial ks k p).eval n =
      (4*n+10+k*14*(n+4)^k+(n+2)^k) +
      (5*((n+2)^k+(n+2)+1)+1+(ks+1)*(n+(n+2)^k*programDepth p+1)+3) := by
  simp [timePolynomial]

theorem bounds (ks k : Nat) (p : Program) (x w : List Bool) :
    let n := (BitstringEncoding.bitEncode (x,w)).length
    let b := x.length+w.length+2
    let q := b^k
    (4*n+8+k*14*(x.length+w.length+4)^k+q) +
      (5*(q+b+1)+1+(ks+1)*(n+q*programDepth p+1)+3) ≤ (timePolynomial ks k p).eval n ∧
    (4*n+9+k*14*(x.length+w.length+4)^k+q)+1+
      (5*(q+b+1)+1+(ks+1)*(n+q*programDepth p+1)+1) ≤ (timePolynomial ks k p).eval n := by
  let n := (BitstringEncoding.bitEncode (x,w)).length
  let b := x.length+w.length+2
  let q := b^k
  have hn : x.length+w.length ≤ n := by
    dsimp [n]
    rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
    omega
  have hb : b ≤ n+2 := by dsimp [b]; omega
  have hc : x.length+w.length+4 ≤ n+4 := by omega
  have hq : q ≤ (n+2)^k := Nat.pow_le_pow_left hb k
  have hw : (x.length+w.length+4)^k ≤ (n+4)^k := Nat.pow_le_pow_left hc k
  have hwork := Nat.mul_le_mul_left (k*14) hw
  have hdepth := Nat.mul_le_mul_right (programDepth p) hq
  have hcore : n+q*programDepth p+1 ≤ n+(n+2)^k*programDepth p+1 := by omega
  have hcore' := Nat.mul_le_mul_left (ks+1) hcore
  have haux : q+b+1 ≤ (n+2)^k+(n+2)+1 := by omega
  have haux' := Nat.mul_le_mul_left 5 haux
  change _ ≤ (timePolynomial ks k p).eval n ∧ _ ≤ (timePolynomial ks k p).eval n
  rw [timePolynomial_eval]
  dsimp [n,b,q] at *
  constructor <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- Every validated fixed numeric pair candidate has one initialized finite
machine computing its totalized Boolean result within the displayed polynomial. -/
theorem boundedNumeric_run (d : InputData) (k : Nat) (p : Program) (output z one : Nat)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (hout : output < d.stackCount)
    (x w : List Bool) :
    let tm := Shared.ComplexityBridge.TM2PairTotalizer.machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one
    ∃ n ≤ (timePolynomial d.stackCount k p).eval (BitstringEncoding.bitEncode (x,w)).length,
      runSteps tm.step n (Turing.initList tm (BitstringEncoding.bitEncode (x,w))) =
        some (Turing.haltList tm [boundedNumeric d k p output z one (x,w)]) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let fuel := (x.length+w.length+2)^k
  obtain ⟨start,hs,hvalid⟩ := Shared.ComplexityBridge.TM2FiniteBoundary.buildStart_valid d bits p hdata hmain
  have hsafe := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hp fuel start hvalid
  have hbound := bounds d.stackCount k p x w
  change buildStart d (BitstringEncoding.bitEncode (x,w)) = some start at hs
  cases hr : run p fuel start with
  | invalid => rw [hr] at hsafe; contradiction
  | timeout r =>
    obtain ⟨n,hn,ht⟩ := Shared.ComplexityBridge.TM2PairTotalizer.pair_timeout_total d k p output z one x w hdata hmain hp start r hs hr
    refine ⟨n,le_trans hn hbound.2,?_⟩
    change run p ((x.length+w.length+2)^k) start = .timeout r at hr
    simpa [boundedNumeric,hs,hr] using ht
  | halted r =>
    obtain ⟨n,hn,ht⟩ := Shared.ComplexityBridge.TM2PairTotalizer.pair_halt_total d k p output z one x w hdata hmain hp hout start r hs hr
    refine ⟨n,le_trans hn hbound.1,?_⟩
    change run p ((x.length+w.length+2)^k) start = .halted r at hr
    simpa [boundedNumeric,hs,hr] using ht

def totalAux (d : InputData) (k : Nat) (p : Program) (output z one : Nat) : Turing.TM2ComputableAux Bool Bool where
  tm := Shared.ComplexityBridge.TM2PairTotalizer.machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

set_option backward.isDefEq.respectTransparency false in
/-- Fixed validated bounded numeric pair evaluation, with timeout and invalid
output mapped to false, belongs to the canonical library's polynomial class. -/
theorem boundedNumeric_isPolyTime (d : InputData) (k : Nat) (p : Program) (output z one : Nat)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (hout : output < d.stackCount) :
    ComplexityTheory.IsPolyTime (boundedNumeric d k p output z one) := by
  let tm := totalAux d k p output z one
  refine ⟨{ toTM2ComputableAux := tm, time := timePolynomial d.stackCount k p, outputsFun := ?_ }⟩
  intro a
  let hrun := boundedNumeric_run d k p output z one hdata hmain hp hout a.1 a.2
  let n := Classical.choose hrun
  have hn := Classical.choose_spec hrun
  refine ⟨⟨n,?_⟩,hn.1⟩
  have hr := hn.2
  rw [runSteps_iterate] at hr
  change (fun o => o.bind tm.tm.step)^[n]
    (some (Turing.initList tm.tm ((BitstringEncoding.bitEncode a).map id))) =
      some (Turing.haltList tm.tm ([boundedNumeric d k p output z one a].map id))
  rw [List.map_id,List.map_id]
  cases a
  exact hr

/-- The numeric machine computes the existing checked pair evaluator with
its timeout and malformed-output cases mapped to false. -/
theorem evaluate_total_eq (c : Candidate) (p : Program) (hdecode : decodeProgram c.1.1 = some p)
    (hdata : validInputData (inputDataOfRaw c.1.2.2) = true)
    (hp : programValid p (inputDataOfRaw c.1.2.2).stackCount (inputDataOfRaw c.1.2.2).states (inputDataOfRaw c.1.2.2).symbols = true)
    (x w : List Bool) :
    (Shared.Codes.TM2PairCandidate.evaluate c x w).getD false =
      boundedNumeric (inputDataOfRaw c.1.2.2) c.1.2.1 p c.2.2.2 c.2.1 c.2.2.1 (x,w) := by
  let d := inputDataOfRaw c.1.2.2
  have hc : candidateValid c = true := by
    simpa [candidateValid,hdecode,inputDataOfRaw] using hp
  let start : Result := ⟨some d.main,d.initialState,
    (List.replicate d.stackCount []).set d.inputStack
      ((BitstringEncoding.bitEncode (x,w)).map (inputBit d.falseSymbol d.trueSymbol))⟩
  have hd : validInputData d = true := hdata
  have hs : buildStart d (BitstringEncoding.bitEncode (x,w)) = some start := by simp [buildStart,hd,start]
  have hi : buildPairInput (c.1.2.2,(x,w)) = some (resultRaw start) := by
    change buildRaw (c.1.2.2,BitstringEncoding.bitEncode (x,w)) = _
    have heq : c.1.2.2 = inputRaw d := by simp [d]
    rw [heq,buildRaw_eq,hs]
    rfl
  have hrun := runEncoded_of_decode c.1.1 p ((x.length+w.length+2)^c.1.2.1) start hdecode
  unfold Shared.Codes.TM2PairCandidate.evaluate
  simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hi]
  change ((runEncoded ((c.1.1,(x.length+w.length+2)^c.1.2.1),resultRaw start)).bind (fun v =>
    if v.1 then Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (c.2.1,c.2.2.1,c.2.2.2,v.2.1,v.2.2.2) else none)).getD false = _
  rw [hrun]
  cases hr : run p ((x.length+w.length+2)^c.1.2.1) start <;>
    simp [outcomeRaw,resultRaw,hr,boundedNumeric,hs,d]

/-- Once its fixed program and input parameters are valid and its output index
is real, a checked pair candidate's default-false totalization is in P. -/
theorem checked_pair_totalized_isPolyTime (c : Candidate) (p : Program)
    (hdecode : decodeProgram c.1.1 = some p)
    (hdata : validInputData (inputDataOfRaw c.1.2.2) = true)
    (hmain : (inputDataOfRaw c.1.2.2).main < p.length)
    (hp : programValid p (inputDataOfRaw c.1.2.2).stackCount (inputDataOfRaw c.1.2.2).states (inputDataOfRaw c.1.2.2).symbols = true)
    (hout : c.2.2.2 < (inputDataOfRaw c.1.2.2).stackCount) :
    ComplexityTheory.IsPolyTime (fun a : List Bool × List Bool => (Shared.Codes.TM2PairCandidate.evaluate c a.1 a.2).getD false) := by
  have h := boundedNumeric_isPolyTime (inputDataOfRaw c.1.2.2) c.1.2.1 p c.2.2.2 c.2.1 c.2.2.1 hdata hmain hp hout
  have heq : (fun a : List Bool × List Bool => (Shared.Codes.TM2PairCandidate.evaluate c a.1 a.2).getD false) =
      boundedNumeric (inputDataOfRaw c.1.2.2) c.1.2.1 p c.2.2.2 c.2.1 c.2.2.1 := by
    funext a
    exact evaluate_total_eq c p hdecode hdata hp a.1 a.2
  rw [heq]
  exact h

/-- Every good verifier has a polynomial-time totalized checker before the
separate original-cutoff test is applied. -/
theorem good_verifier_checker_poly (v : Shared.NPCONP.TM2Verifier.Verifier)
    (hgood : ∀ x, Shared.NPCONP.TM2Verifier.test v x = true) :
    ComplexityTheory.IsPolyTime (fun a : List Bool × List Bool => (Shared.Codes.TM2PairCandidate.evaluate v.2 a.1 a.2).getD false) := by
  obtain ⟨p,hdecode,hdata,hmain,hp,hout,_⟩ := Shared.ComplexityBridge.TM2VerifierValidity.good_has_valid_parameters v hgood
  exact checked_pair_totalized_isPolyTime v.2 p hdecode hdata hmain hp hout

/-- The original witness cutoff masks the checker without changing its clock. -/
def cutoffMask (terms : Shared.Codes.NumericPolynomial.Terms) (R : (List Bool × List Bool) → Bool)
    (a : List Bool × List Bool) : Bool :=
  if a.2.length ≤ Shared.Codes.NumericPolynomial.eval terms a.1.length then R a else false

/-- The exact remaining closure obligation: compute the fixed polynomial
cutoff, compare it to witness length, and combine the result with a canonical
polynomial-time pair checker. -/
def CutoffMaskClosed : Prop :=
  ∀ (terms : Shared.Codes.NumericPolynomial.Terms) (R : (List Bool × List Bool) → Bool),
    ComplexityTheory.IsPolyTime R → ComplexityTheory.IsPolyTime (cutoffMask terms R)

theorem verifierRelation_mask (v : Shared.NPCONP.TM2Verifier.Verifier) :
    Shared.ComplexityBridge.TM2WholePair.verifierRelation v =
      cutoffMask v.1.2 (fun a => (Shared.Codes.TM2PairCandidate.evaluate v.2 a.1 a.2).getD false) := by
  funext a
  by_cases h : a.2.length ≤ Shared.Codes.NumericPolynomial.eval v.1.2 a.1.length <;>
    simp [Shared.ComplexityBridge.TM2WholePair.verifierRelation,Shared.NPCONP.TM2Verifier.verify,
      Shared.NPCONP.TM2Verifier.cutoff,cutoffMask,h]

/-- The numeric wrapper obligation is reduced to the explicit cutoff-mask
closure; the fixed-clock checker is already proved polynomial-time. -/
theorem goodVerifierRelationPoly_of_cutoff (hcutoff : CutoffMaskClosed) :
    Shared.ComplexityBridge.TM2WholePair.GoodVerifierRelationPoly := by
  intro v hgood
  rw [verifierRelation_mask]
  exact hcutoff v.1.2 _ (good_verifier_checker_poly v hgood)

/-- The NP-versus-coNP endpoint remains conditional on cutoff-mask closure,
completeness, reduction closure, and the later event-refinement certificate. -/
theorem npconp_certified_cutoff_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (np_pullback : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.NP)
    (hcutoff : CutoffMaskClosed) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.ComplexityBridge.TM2WholePair.npconp_certified_conditional cert complete np_pullback
    (goodVerifierRelationPoly_of_cutoff hcutoff)

end Shared.ComplexityBridge.TM2PairTotalPoly
