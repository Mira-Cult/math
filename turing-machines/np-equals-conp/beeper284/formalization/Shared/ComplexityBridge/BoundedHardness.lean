import Shared.ComplexityBridge.CNFDisjunction
import Shared.ComplexityBridge.TM2PreparedVerify

/-! Integration of the proved bounded-witness CNF reduction with the pinned
Google NP definition. Two explicit remaining obligations are a quantitative
canonical-verifier-to-finite-program compiler and polynomial-time execution of
the actual CNF generator. No completeness or endpoint is asserted without them. -/
namespace Shared.ComplexityBridge.BoundedHardness
open ComplexityTheory
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CNFDisjunction
open Shared.ComplexityBridge.CanonicalClasses

/-- One fixed numerical clock bounds every encoded pair with a witness under
`bound`. It includes both the delimited public input and the witness encoding. -/
def pairInputBound (bound : Polynomial Nat) (x : List Bool) : Nat :=
  6*x.length+1+3*bound.eval x.length

def commonFuel (bound time : Polynomial Nat) (x : List Bool) : Nat :=
  time.eval (pairInputBound bound x)

/-- The actual bitstring returned by the reduction. -/
def reduction (program : Program) (bound time : Polynomial Nat) (x : List Bool) : List Bool :=
  BitstringEncoding.bitEncode (boundedPairFormula program x (bound.eval x.length) (commonFuel bound time x))

/-- This is the missing quantitative translation, not a proved model bridge.
The fixed program and polynomial must compute the relation on every canonical
pair encoding, including false outputs and all finite input lengths. -/
def FiniteVerifierCompiler : Prop :=
  ∀ R : (List Bool × List Bool) → Bool, IsPolyTime R →
    ∃ (program : Program) (time : Polynomial Nat), ∀ x w,
      bounded program (BitstringEncoding.bitEncode (x,w))
        (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (R (x,w))

/-- Narrower model-translation obligation against the already constructed,
validated numeric TM2 pair candidates. It must preserve `none`, false and true
outputs and use one polynomial in the canonical encoded pair length. -/
def NumericPairCompiler : Prop :=
  ∀ c : Shared.Codes.TM2Candidate.Candidate,
    Shared.Codes.TM2CheckedCandidate.candidateValid c = true →
    ∃ (program : Program) (time : Polynomial Nat), ∀ x w,
      bounded program (BitstringEncoding.bitEncode (x,w))
        (time.eval (BitstringEncoding.bitEncode (x,w)).length) =
      Shared.Codes.TM2PairCandidate.evaluate c x w

/-- Existing canonical TM2 candidate coverage discharges the logical part of
the verifier translation once that quantitative model adapter is supplied. -/
theorem finiteVerifierCompiler_of_numeric (hadapter : NumericPairCompiler) : FiniteVerifierCompiler := by
  intro R hR
  obtain ⟨c,hvalid,hcorrect⟩ := Shared.Codes.TM2PairCandidate.canonicalPoly_covers R hR
  obtain ⟨program,time,hsim⟩ := hadapter c hvalid
  refine ⟨program,time,?_⟩
  intro x w
  rw [hsim,hcorrect]

/-- This is the separate missing execution-cost theorem. `IsPolyTime` uses
Google's encodings for both the input and the returned bitstring. -/
def GeneratorPolyTime : Prop :=
  ∀ (program : Program) (bound time : Polynomial Nat), IsPolyTime (reduction program bound time)

theorem bounded_mono (program : Program) (input : List Bool) (small large : Nat) (b : Bool)
    (hle : small ≤ large) (h : bounded program input small = some b) :
    bounded program input large = some b := by
  obtain ⟨t,ht,hr⟩ := (bounded_iff_result program input small b).1 h
  exact (bounded_iff_result program input large b).2 ⟨t,le_trans ht hle,hr⟩

theorem encoded_pair_le (bound : Polynomial Nat) (x w : List Bool) (hw : w.length ≤ bound.eval x.length) :
    (BitstringEncoding.bitEncode (x,w)).length ≤ pairInputBound bound x := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
  dsimp [pairInputBound]
  omega

/-- A translated verifier is correct at one common input-dependent clock for
all witnesses under the original cutoff. -/
theorem commonFuel_correct (R : (List Bool × List Bool) → Bool)
    (program : Program) (bound time : Polynomial Nat)
    (hprogram : ∀ x w, bounded program (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (R (x,w))) :
    ∀ x w, w.length ≤ bound.eval x.length →
      bounded program (BitstringEncoding.bitEncode (x,w)) (commonFuel bound time x) = some (R (x,w)) := by
  intro x w hw
  apply bounded_mono program _ _ _ (R (x,w))
  · exact Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono time (encoded_pair_le bound x w hw)
  · exact hprogram x w

/-- The concrete formula computes any relation with a proved finite-program
implementation and the original polynomial witness cutoff. -/
theorem reduction_correct (R : (List Bool × List Bool) → Bool)
    (program : Program) (bound time : Polynomial Nat)
    (hprogram : ∀ x w, bounded program (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (R (x,w))) (x : List Bool) :
    sat (reduction program bound time x) = true ↔
      ∃ w : List Bool, w.length ≤ bound.eval x.length ∧ R (x,w) = true := by
  unfold reduction
  exact sat_boundedPairFormula_of_verifier program x (bound.eval x.length) (commonFuel bound time x)
    (fun x w => R (x,w)) (commonFuel_correct R program bound time hprogram x)

/-- These two precise, separately named obligations imply the actual uniform
canonical NP-to-SAT reductions. This is conditional, not a completeness claim. -/
theorem satHard_of_compiler_and_generator (hcompiler : FiniteVerifierCompiler)
    (hgenerator : GeneratorPolyTime) : Shared.ComplexityBridge.CNFWitness.SatHard := by
  intro L hL
  obtain ⟨bound,R,hR,hL⟩ := hL
  obtain ⟨program,time,hprogram⟩ := hcompiler R hR
  refine ⟨reduction program bound time,hgenerator program bound time,?_⟩
  intro x
  have hr := reduction_correct R program bound time hprogram x
  have htruth : L x = true ↔ sat (reduction program bound time x) = true := by
    exact (hL x).trans hr.symm
  cases h₁ : L x <;> cases h₂ : sat (reduction program bound time x) <;> simp_all

/-- An explicit polynomial for the *encoded output length* of `reduction`.
This is not a running-time bound. The polynomial uses the original witness
polynomial, the verifier clock and the fixed finite program. -/
noncomputable def outputBoundPolynomial (program : Program) (bound time : Polynomial Nat) : Polynomial Nat :=
  let x : Polynomial Nat := Polynomial.X
  let b := bound
  let t := time.comp (Polynomial.C 6*x+Polynomial.C 1+Polynomial.C 3*b)
  let k := Polynomial.C 6*x+Polynomial.C 1+Polynomial.C 3*b+t
  let s : Polynomial Nat := Polynomial.C (program.length+3)
  let w := s+(Polynomial.C 2*k+Polynomial.C 1)
  let g := t*((Polynomial.C 2*(Polynomial.C 2+Polynomial.C 4*s)+
    (Polynomial.C 1+Polynomial.C 4*(Polynomial.C 2*k+Polynomial.C 1)))+
      s*(Polynomial.C 2+Polynomial.C 4*s))
  let clauses := Polynomial.C 2*b+w+Polynomial.C 3*g+Polynomial.C 1
  let vars := w+Polynomial.C 3*b+g
  Polynomial.C 3*((Polynomial.C 1+(b+Polynomial.C 1)*clauses)*
    (Polynomial.C 2*((b+Polynomial.C 1+Polynomial.C 4)*
      (Polynomial.C 4*(Polynomial.C 2*(vars+(b+Polynomial.C 1)+Polynomial.C 1))+Polynomial.C 5))+
        Polynomial.C 1))

theorem outputBoundPolynomial_eval (program : Program) (bound time : Polynomial Nat) (x : List Bool) :
    (outputBoundPolynomial program bound time).eval x.length =
      3*((1+(bound.eval x.length+1)*maxClauses program x (bound.eval x.length) (commonFuel bound time x))*
        (2*((bound.eval x.length+1+4)*
          (4*(2*(maxVariables program x (bound.eval x.length) (commonFuel bound time x)+
            (bound.eval x.length+1)+1))+5))+1)) := by
  simp [outputBoundPolynomial,commonFuel,pairInputBound,maxClauses,maxVariables,maxWidth,maxStates,maxGates,maxWindow,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp]

/-- The serialized CNF output, including the outer Google list encoding,
has a polynomial bound in the full canonical encoded input length. -/
theorem reduction_encoded_output_bound (program : Program) (bound time : Polynomial Nat) (x : List Bool) :
    (BitstringEncoding.bitEncode (reduction program bound time x)).length ≤
      (outputBoundPolynomial program bound time).eval (BitstringEncoding.bitEncode x).length := by
  have hraw := boundedPairFormula_encoded_length program x (bound.eval x.length) (commonFuel bound time x)
  have hout := Nat.mul_le_mul_left 3 hraw
  have hsize : (BitstringEncoding.bitEncode (reduction program bound time x)).length ≤
      (outputBoundPolynomial program bound time).eval x.length := by
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length,outputBoundPolynomial_eval]
    exact hout
  have hx : x.length ≤ (BitstringEncoding.bitEncode x).length := by
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length]
    omega
  exact le_trans hsize (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono _ hx)

/-- Separate later machine bindings inherit the conditional equivalences. -/
theorem pnp_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (hcompiler : FiniteVerifierCompiler) (hgenerator : GeneratorPolyTime) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.ComplexityBridge.TM2PreparedVerify.pnp_of_sat_hard cert
    (satHard_of_compiler_and_generator hcompiler hgenerator)

theorem npconp_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (hcompiler : FiniteVerifierCompiler) (hgenerator : GeneratorPolyTime) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.ComplexityBridge.TM2PreparedVerify.npconp_of_sat_hard cert
    (satHard_of_compiler_and_generator hcompiler hgenerator)

/-- The same separate endpoints with the model obligation stated against the
existing numeric TM2 candidate universe. -/
theorem pnp_of_numeric_adapter {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (hadapter : NumericPairCompiler) (hgenerator : GeneratorPolyTime) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  pnp_conditional cert (finiteVerifierCompiler_of_numeric hadapter) hgenerator

theorem npconp_of_numeric_adapter {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (hadapter : NumericPairCompiler) (hgenerator : GeneratorPolyTime) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  npconp_conditional cert (finiteVerifierCompiler_of_numeric hadapter) hgenerator

namespace Fixtures
def alwaysTrue : Program := [((false,false,0,2),(false,false,0,2))]

theorem alwaysTrue_correct (x w : List Bool) :
    bounded alwaysTrue (BitstringEncoding.bitEncode (x,w))
      ((Polynomial.C 1 : Polynomial Nat).eval (BitstringEncoding.bitEncode (x,w)).length) = some true := by
  simp [alwaysTrue,bounded,run,advance,step,initial]

example : sat (reduction alwaysTrue (Polynomial.C 0) (Polynomial.C 1) []) = true := by
  apply (reduction_correct (fun _ => true) alwaysTrue (Polynomial.C 0) (Polynomial.C 1) alwaysTrue_correct []).2
  exact ⟨[],by simp,rfl⟩

example : (BitstringEncoding.bitEncode (reduction alwaysTrue (Polynomial.C 0) (Polynomial.C 1) [])).length ≤
    (outputBoundPolynomial alwaysTrue (Polynomial.C 0) (Polynomial.C 1)).eval
      (BitstringEncoding.bitEncode ([] : List Bool)).length :=
  reduction_encoded_output_bound _ _ _ _
end Fixtures

end Shared.ComplexityBridge.BoundedHardness
