import Shared.Codes.NumericPolynomial
import Shared.Codes.VerifierPrograms
import Shared.ComplexityBridge.ParserComputability
import Shared.Beeping.ComparisonImplementation

/-! Checked numeric verifier comparisons for total complement-SAT.
The original polynomial witness cutoff is stored as finite monomial data; the
outer search exponent may be larger but extra witnesses are rejected. The
controller and certified-machine theorems are conditional on their displayed
hypotheses and do not discharge a complexity equivalence or bit-cost bridge. -/
namespace Shared.NPCONP.TM2Verifier
open Shared.Codes.TM2Candidate Shared.Codes.TM2CheckedCandidate
open Shared.Codes.NumericPolynomial Shared.Codes.VerifierPrograms
open Shared.ComplexityBridge.CNF

/-- Outer witness exponent, original polynomial cutoff, and checked pair
checker. The cutoff is retained even when the outer exponent is enlarged. -/
abbrev Verifier := (Nat × Terms) × Candidate

def witnessBound (v : Verifier) (x : List Bool) : Nat := (x.length+2)^v.1.1
def cutoff (v : Verifier) (x : List Bool) : Nat := Shared.Codes.NumericPolynomial.eval v.1.2 x.length

def verify (v : Verifier) (x w : List Bool) : Option Bool :=
  if w.length ≤ cutoff v x then Shared.Codes.TM2PairCandidate.evaluate v.2 x w else some false

def terminates (v : Verifier) (x : List Bool) : Bool :=
  (witnesses (witnessBound v x)).all fun w => (verify v x w).isSome

def accepts (v : Verifier) (x : List Bool) : Bool :=
  (witnesses (witnessBound v x)).any fun w => verify v x w == some true

def test (v : Verifier) (x : List Bool) : Bool :=
  candidateValid v.2 && terminates v x && (accepts v x == complementSat x)

theorem witnessBound_primrec : Primrec₂ witnessBound := by
  exact (Shared.Codes.FinitePrograms.clock_primrec.comp Primrec.snd
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to₂

theorem cutoff_primrec : Primrec₂ cutoff := by
  exact (Shared.Codes.NumericPolynomial.eval_primrec.comp
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.list_length.comp Primrec.snd)).to₂

theorem verify_primrec : Primrec (fun p : (Verifier × List Bool) × List Bool => verify p.1.1 p.1.2 p.2) := by
  let A := (Verifier × List Bool) × List Bool
  have hcut : Primrec (fun p : A => cutoff p.1.1 p.1.2) := cutoff_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hlen : Primrec (fun p : A => p.2.length) := Primrec.list_length.comp Primrec.snd
  have hc : Primrec (fun p : A => Shared.Codes.TM2PairCandidate.evaluate p.1.1.2 p.1.2 p.2) :=
    Shared.Codes.TM2PairCandidate.evaluate_primrec.comp (Primrec.pair
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  exact Primrec.ite (Primrec.nat_le.comp hlen hcut) hc (Primrec.const (some false))

theorem witnessList_primrec : Primrec (fun p : Verifier × List Bool => witnesses (witnessBound p.1 p.2)) :=
  witnesses_primrec.comp witnessBound_primrec

theorem terminates_primrec : Primrec₂ terminates := by
  have hg : Primrec₂ (fun (p : Verifier × List Bool) (w : List Bool) => (verify p.1 p.2 w).isSome) :=
    (Primrec.option_isSome.comp verify_primrec).to₂
  exact (Shared.ComplexityBridge.CNF.list_all_primrec witnessList_primrec hg).to₂

theorem accepts_primrec : Primrec₂ accepts := by
  have hg : Primrec₂ (fun (p : Verifier × List Bool) (w : List Bool) => verify p.1 p.2 w == some true) := by
    have h := (Primrec.beq.comp verify_primrec (Primrec.const (some true : Option Bool))).to₂
    apply h.of_eq
    intro p w
    cases verify p.1 p.2 w with
    | none => rfl
    | some b => cases b <;> rfl
  exact (Shared.ComplexityBridge.CNF.list_any_primrec witnessList_primrec hg).to₂

theorem test_computable : Computable₂ test := by
  let A := Verifier × List Bool
  have hv : Computable (fun p : A => candidateValid p.1.2) :=
    candidateValid_primrec.to_comp.comp (Computable.snd.comp Computable.fst)
  have ht : Computable (fun p : A => terminates p.1 p.2) := terminates_primrec.to_comp
  have ha : Computable (fun p : A => accepts p.1 p.2) := accepts_primrec.to_comp
  have hr : Computable (fun p : A => complementSat p.2) :=
    Shared.ComplexityBridge.ParserComputability.complementSat_computable.comp Computable.snd
  exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hv ht) (Primrec.beq.to_comp.comp ha hr)).to₂

theorem terminates_iff (v : Verifier) (x : List Bool) : terminates v x = true ↔
    ∀ w, w.length ≤ witnessBound v x → (verify v x w).isSome = true := by
  simp [terminates, List.all_eq_true, mem_witnesses_iff]

theorem accepts_iff (v : Verifier) (x : List Bool) : accepts v x = true ↔
    ∃ w, w.length ≤ witnessBound v x ∧ verify v x w = some true := by
  simp [accepts, List.any_eq_true, mem_witnesses_iff]

theorem test_iff (v : Verifier) (x : List Bool) : test v x = true ↔
    candidateValid v.2 = true ∧
    (∀ w, w.length ≤ witnessBound v x → (verify v x w).isSome = true) ∧
    ((∃ w, w.length ≤ witnessBound v x ∧ verify v x w = some true) ↔ complementSat x = true) := by
  have hb : (accepts v x == complementSat x) = true ↔ (accepts v x = true ↔ complementSat x = true) := by
    cases accepts v x <;> cases complementSat x <;> simp
  rw [← terminates_iff, ← accepts_iff, ← hb]
  simp [test, Bool.and_eq_true, and_assoc]

theorem invalid_fails (v : Verifier) (x : List Bool) (h : candidateValid v.2 = false) :
    test v x = false := by simp [test, h]

theorem timeout_fails (v : Verifier) (x w : List Bool)
    (hw : w.length ≤ witnessBound v x) (ht : verify v x w = none) : test v x = false := by
  have hterm : terminates v x = false := by
    cases h : terminates v x with
    | false => rfl
    | true =>
      have hall := (terminates_iff v x).1 h w hw
      simp [ht] at hall
  simp [test, hterm]

theorem cutoff_rejects (v : Verifier) (x w : List Bool) (h : cutoff v x < w.length) :
    verify v x w = some false := by simp [verify, Nat.not_le_of_gt h]

theorem cutoff_search (v : Verifier) (x : List Bool) :
    (∃ w, w.length ≤ witnessBound v x ∧ verify v x w = some true) ↔
      ∃ w, w.length ≤ witnessBound v x ∧ w.length ≤ cutoff v x ∧
        Shared.Codes.TM2PairCandidate.evaluate v.2 x w = some true := by
  constructor
  · rintro ⟨w,hw,hv⟩
    by_cases hc : w.length ≤ cutoff v x
    · exact ⟨w,hw,hc,by simpa [verify,hc] using hv⟩
    · simp [verify,hc] at hv
  · rintro ⟨w,hw,hc,he⟩
    exact ⟨w,hw,by simpa [verify,hc] using he⟩

/-- Every canonical NP language has a checked numeric verifier with a fixed
outer exponent and an exact executable copy of the original witness cutoff. -/
theorem canonicalNP_covers (L : ComplexityTheory.DecisionProblem) (hL : L ∈ ComplexityTheory.NP) :
    ∃ v : Verifier, candidateValid v.2 = true ∧ ∀ x,
      terminates v x = true ∧ (accepts v x = true ↔ L x = true) := by
  obtain ⟨p,R,hR,hrel⟩ := hL
  obtain ⟨terms,hterms⟩ := Shared.Codes.NumericPolynomial.polynomial_represented p
  obtain ⟨b,hbound⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent p
  obtain ⟨c,hvalid,hcorrect⟩ := Shared.Codes.TM2PairCandidate.canonicalPoly_covers R hR
  let v : Verifier := ((b,terms),c)
  refine ⟨v,hvalid,?_⟩
  intro x
  have hverify (w : List Bool) : verify v x w =
      some (if w.length ≤ p.eval x.length then R (x,w) else false) := by
    by_cases hw : w.length ≤ p.eval x.length <;> simp [verify,cutoff,v,hterms,hcorrect,hw]
  have hterm : terminates v x = true := by
    apply (terminates_iff v x).2
    intro w hw
    rw [hverify]
    simp
  refine ⟨hterm,?_⟩
  rw [accepts_iff, cutoff_search]
  have hx : (L x = true) ↔ ∃ w, w.length ≤ p.eval x.length ∧ R (x,w) = true := hrel x
  rw [hx]
  constructor
  · rintro ⟨w,hw,hcut,heval⟩
    refine ⟨w,?_,?_⟩
    · simpa [cutoff,v,hterms] using hcut
    · exact Option.some.inj (heval.symm.trans (hcorrect x w)) |>.symm
  · rintro ⟨w,hcut,hRtrue⟩
    refine ⟨w,?_,?_,?_⟩
    · change w.length ≤ (x.length+2)^b
      exact le_trans hcut (hbound x.length)
    · simpa [cutoff,v,hterms] using hcut
    · rw [hcorrect, hRtrue]

theorem complementSat_in_NP_covers (h : complementSat ∈ ComplexityTheory.NP) :
    ∃ v : Verifier, ∀ x, test v x = true := by
  obtain ⟨v,hvalid,h⟩ := canonicalNP_covers complementSat h
  refine ⟨v,?_⟩
  intro x
  obtain ⟨ht,ha⟩ := h x
  apply (test_iff v x).2
  exact ⟨hvalid, (terminates_iff v x).1 ht, by simpa [accepts_iff] using ha⟩

def decode (n : Nat) : Option Verifier := Encodable.decode n

theorem decode_primrec : Primrec decode := Primrec.decode

theorem decode_coverage (v : Verifier) : decode (Encodable.encode v) = some v := Encodable.encodek v

def optionTest {α : Type} (decoded : Option α) (f : α → Bool) : Bool :=
  match decoded with | none => false | some a => f a

def compare (e n : Nat) : Bool :=
  optionTest (decode e) (fun v => test v (Shared.Codes.Inputs.inputAt n))

theorem compare_computable : Computable₂ compare := by
  have ht : Computable (fun p : Verifier × Nat => test p.1 (Shared.Codes.Inputs.inputAt p.2)) :=
    test_computable.comp Computable.fst (Shared.Codes.Inputs.computable.comp Computable.snd)
  have h := Computable.option_casesOn (decode_primrec.to_comp.comp Computable.fst) (Computable.const false)
    (ht.comp (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))).to₂
  apply h.of_eq
  rintro ⟨e,n⟩
  unfold compare optionTest
  cases decode e <;> rfl

theorem optionTest_spec {α : Type} (decoded : Option α) (f : α → Bool) :
    optionTest decoded f = true ↔ ∃ a, decoded = some a ∧ f a = true := by
  cases decoded <;> simp [optionTest]

theorem compare_iff (e n : Nat) : compare e n = true ↔ ∃ v,
    decode e = some v ∧ test v (Shared.Codes.Inputs.inputAt n) = true := by
  unfold compare
  exact optionTest_spec _ _

theorem good_iff (e : Nat) : (∀ n, compare e n = true) ↔ ∃ v,
    decode e = some v ∧ ∀ x, test v x = true := by
  constructor
  · intro h
    obtain ⟨v,hv,_⟩ := (compare_iff e 0).1 (h 0)
    refine ⟨v,hv,?_⟩
    intro x
    obtain ⟨n,hn⟩ := Shared.Codes.Inputs.covers x
    obtain ⟨v',hv',ht⟩ := (compare_iff e n).1 (h n)
    have heq : v' = v := Option.some.inj (hv'.symm.trans hv)
    subst v'
    simpa [hn] using ht
  · rintro ⟨v,hv,h⟩ n
    exact (compare_iff e n).2 ⟨v,hv,h _⟩

theorem controller_silent_iff :
    (Shared.Beeping.Controller.system compare 0).EventuallySilent ↔
      ∃ v : Verifier, ∀ x, test v x = true := by
  rw [Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good]
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨v,_,hv⟩ := (good_iff e).1 he
    exact ⟨v,hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨Encodable.encode v,(good_iff _).2 ⟨v,decode_coverage v,hv⟩⟩

theorem complementSat_in_NP_silence (h : complementSat ∈ ComplexityTheory.NP) :
    (Shared.Beeping.Controller.system compare 0).EventuallySilent :=
  controller_silent_iff.2 (complementSat_in_NP_covers h)

theorem equality_implies_silence (hsat : sat ∈ ComplexityTheory.NP)
    (heq : ComplexityTheory.NP = ComplexityTheory.coNP) :
    (Shared.Beeping.Controller.system compare 0).EventuallySilent := by
  apply complementSat_in_NP_silence
  rw [heq]
  change complementSatᶜ ∈ ComplexityTheory.NP
  have hc : complementSat = satᶜ := rfl
  rw [hc]
  simpa using hsat

/-- A later finite table must supply the progress-sensitive comparison
certificate; it is not constructed or assumed here. -/
theorem certified_machine_silent_iff {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate compare 0 M) :
    M.system.EventuallySilent ↔ ∃ v : Verifier, ∀ x, test v x = true := by
  calc
    M.system.EventuallySilent ↔ ∃ e, Shared.Beeping.Controller.Good compare e := by
      simpa using cert.eventuallySilent_iff_good
    _ ↔ (Shared.Beeping.Controller.system compare 0).EventuallySilent :=
      (Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good compare).symm
    _ ↔ _ := controller_silent_iff

theorem certified_equality_forward {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate compare 0 M)
    (hsat : sat ∈ ComplexityTheory.NP) (heq : ComplexityTheory.NP = ComplexityTheory.coNP) :
    M.system.EventuallySilent :=
  (certified_machine_silent_iff cert).2 (controller_silent_iff.1 (equality_implies_silence hsat heq))

example : verify ((1,[]),((0,0,((1,1,2),(1,0,0),(0,0,1))),(0,1,0))) [] [true] = some false := by decide
example : cutoff ((1,[]),((0,0,((1,1,2),(1,0,0),(0,0,1))),(0,1,0))) [] = 0 := by decide

end Shared.NPCONP.TM2Verifier
