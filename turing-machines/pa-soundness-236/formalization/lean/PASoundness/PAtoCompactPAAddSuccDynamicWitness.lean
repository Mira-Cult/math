import PASoundness.PAtoCompactPAAddSuccDynamicRaw
import PASoundness.PAtoCompactSuccessorQuotientExistence
import PASoundness.PAtoCompactRawSuccessorBinderBridge
import PASoundness.PAtoCompactSuccWitnessVacuityDynamic
import PASoundness.PAtoCompactTermGraphBinderRange

/-! Candidate successors and the addition-successor diamond at arbitrary
input names and an explicitly high allocation base. The same new output is
retained for its quotient-successor and addition relations. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccDynamicWitness
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccWitnessVacuityDynamic
open PASoundness.PAtoCompactSuccessorQuotientExistence PASoundness.PAtoCompactRawSuccessorBinderBridge
open PASoundness.PAtoCompactPAAddSuccDynamicSyntax PASoundness.PAtoCompactPAAddSuccDynamicRaw
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def body (b x y z m n : Nat) : Formula :=
  andF (domainAt b m) (andF (domainAt b n)
    (andF (succAt b y m) (andF (succAt b z n) (addAt b x m n))))
def result (b x y z m n : Nat) : Formula := .ex m (.ex n (body b x y z m n))
def rawBody (b x o : Nat) : Formula := andF (namedSuccessor x o (b+10)) (domainAt b o)

theorem body_not_binder (b x y z m n k : Nat) (hk : k < b+2) :
    k ∉ (body b x y z m n).binders := by
  intro h
  simp only [body, andF_binders, Finset.mem_union] at h
  rcases h with h | h | h | h | h
  · have hh := domainAt_private b m k h; omega
  · have hh := domainAt_private b n k h; omega
  · have hh := succAt_private b y m k h; omega
  · have hh := succAt_private b z n k h; omega
  · have hh := addAt_private b x m n k h; omega

def vac_domain (b a k : Nat) (hka : k ≠ a) :
    KDerivation (imp (domainAt b a).encode (allCode k (domainAt b a).encode)) := by
  apply free_vacuity
  intro h
  have hh := domainAt_free b a h
  simp [hka] at hh

def vac_add (b x y z k : Nat) (hkx : k ≠ x) (hky : k ≠ y) (hkz : k ≠ z) :
    KDerivation (imp (addAt b x y z).encode (allCode k (addAt b x y z).encode)) := by
  apply free_vacuity
  intro h
  have hh := addAt_free b x y z h
  simp [hkx,hky,hkz] at hh

def vac_rawBody (b x o k : Nat) (hkx : k ≠ x) (hko : k ≠ o) :
    KDerivation (imp (rawBody b x o).encode (allCode k (rawBody b x o).encode)) := by
  apply free_vacuity
  intro h
  simp only [rawBody, andF_free, Finset.mem_union] at h
  rcases h with h | h
  · have hh := raw_free x o (b+10) h
    simp [hkx,hko] at hh
  · have hh := domainAt_free b o h
    simp [hko] at hh

theorem result_free_m (b x y z m n : Nat) : m ∉ (result b x y z m n).free := by
  simp [result, Formula.free]
theorem result_free_n (b x y z m n : Nat) : n ∉ (result b x y z m n).free := by
  simp [result, Formula.free]

/-- Candidate values y,z and x+y=z admit a successor m of y and a successor n
of z, both candidate, such that x+m=n. All inputs may alias; m,n are fresh
syntactic labels for the two existential binders. -/
noncomputable def dynamic_exists (b x y z m n : Nat)
    (hb : 46 ≤ b) (hx : x < b) (hy : y < b) (hz : z < b)
    (hm : m < b) (hn : n < b)
    (hmx : m ≠ x) (hmy : m ≠ y) (hmz : m ≠ z)
    (hnx : n ≠ x) (hny : n ≠ y) (hnz : n ≠ z) (hmn : m ≠ n) :
    KDerivation (imp (domainAt b y).encode (imp (domainAt b z).encode
      (imp (addAt b x y z).encode (result b x y z m n).encode))) := by
  let D1 := (domainAt b y).encode
  let D2 := (domainAt b z).encode
  let A := (addAt b x y z).encode
  let Wm := (rawBody b y m).encode
  let Wn := (rawBody b z n).encode
  let R := (result b x y z m n).encode
  have heM : KDerivation (imp D1 (existsCode m Wm)) := by
    simpa [D1, Wm, rawBody, namedSuccessor, namedSuccessorBody, namedBoth,
      namedEither, successorCode, andF, Formula.not, Formula.encode, both, neg, either] using
      raw_candidate_successor b y m (by omega) hm (Ne.symm hmy)
  have heN : KDerivation (imp D2 (existsCode n Wn)) := by
    simpa [D2, Wn, rawBody, namedSuccessor, namedSuccessorBody, namedBoth,
      namedEither, successorCode, andF, Formula.not, Formula.encode, both, neg, either] using
      raw_candidate_successor b z n (by omega) hn (Ne.symm hnz)
  have hp : KDerivation (imp D1 (imp D2 (imp A (imp Wm (imp Wn R))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [Wn,Wm,A,D2,D1]
    have hwn : Context Γ Wn := .head _ _
    have hwm : Context Γ Wm := .hypothesis (by simp [Γ])
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hd2 : Context Γ D2 := .hypothesis (by simp [Γ])
    have hd1 : Context Γ D1 := .hypothesis (by simp [Γ])
    have hsm : Context Γ (successorCode y m (b+10)) := Context.conjunctionLeft hwm
    have hdm : Context Γ (domainAt b m).encode := Context.conjunctionRight hwm
    have hsn : Context Γ (successorCode z n (b+10)) := Context.conjunctionLeft hwn
    have hdn : Context Γ (domainAt b n).encode := Context.conjunctionRight hwn
    have hq1 : Context Γ (succAt b y m).encode := .mp hdm (.mp hsm (.mp hd1
      (.closed (quotient_of_arbitrary_raw b y m (b+10) (by omega) hm (by omega) (by omega)))))
    have hq2 : Context Γ (succAt b z n).encode := .mp hdn (.mp hsn (.mp hd2
      (.closed (quotient_of_arbitrary_raw b z n (b+10) (by omega) hn (by omega) (by omega)))))
    have hstep := dynamic_raw_step b (b+10) x y z m n hb (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hadd : Context Γ (addAt b x m n).encode := by
      have hh := Context.mp ha (Context.mp hsn (Context.mp hsm (Context.mp hd2 (Context.mp hd1 (.closed hstep)))))
      simpa [assignedFrame, Formula.encode, namedSuccessor, namedSuccessorBody,
        namedBoth, namedEither, successorCode, both, neg, either] using hh
    have hbody : Context Γ (body b x y z m n).encode := by
      exact Context.conjunctionIntro hdm (Context.conjunctionIntro hdn
        (Context.conjunctionIntro hq1 (Context.conjunctionIntro hq2 hadd)))
    have hmB := body_not_binder b x y z m n m (by omega)
    have hnB := body_not_binder b x y z m n n (by omega)
    have hnI := existsIntroduce n (body b x y z m n) hnB
    have hmI := existsIntroduce m (.ex n (body b x y z m n)) (by simpa [Formula.binders, hmn] using hmB)
    exact .mp (.mp hbody (.closed hnI)) (.closed hmI)
  have hN : KDerivation (imp D1 (imp D2 (imp A (imp Wm R)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [Wm,A,D2,D1]
    have hwm : Context Γ Wm := .head _ _
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hd2 : Context Γ D2 := .hypothesis (by simp [Γ])
    have hd1 : Context Γ D1 := .hypothesis (by simp [Γ])
    have hex : Context Γ (existsCode n Wn) := .mp hd2 (.closed heN)
    have hpoint : Context Γ (imp Wn R) := .mp hwm (.mp ha (.mp hd2 (.mp hd1 (.closed hp))))
    have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode n h)) := by
      intro h hh
      simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
      by_cases h0 : h = Wm
      · subst h; exact vac_rawBody b y m n hny (Ne.symm hmn)
      by_cases h1 : h = A
      · subst h; exact vac_add b x y z n hnx hny hnz
      by_cases h2 : h = D2
      · subst h; exact vac_domain b z n hnz
      have h3 : h = D1 := by simpa [h0,h1,h2] using hh
      subst h; exact vac_domain b y n hny
    have hall := Context.generalize n hv hpoint
    exact Context.existsElim (free_vacuity n (result b x y z m n) (result_free_n b x y z m n)) hall hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [A,D2,D1]
  have ha : Context Γ A := .head _ _
  have hd2 : Context Γ D2 := .hypothesis (by simp [Γ])
  have hd1 : Context Γ D1 := .hypothesis (by simp [Γ])
  have hex : Context Γ (existsCode m Wm) := .mp hd1 (.closed heM)
  have hpoint : Context Γ (imp Wm R) := .mp ha (.mp hd2 (.mp hd1 (.closed hN)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode m h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h0 : h = A
    · subst h; exact vac_add b x y z m hmx hmy hmz
    by_cases h1 : h = D2
    · subst h; exact vac_domain b z m hmz
    have h2 : h = D1 := by simpa [h0,h1] using hh
    subst h; exact vac_domain b y m hmy
  have hall := Context.generalize m hv hpoint
  exact Context.existsElim (free_vacuity m (result b x y z m n) (result_free_m b x y z m n)) hall hex


theorem dynamic_exists_certificate (b x y z m n : Nat)
    (hb : 46 ≤ b) (hx : x < b) (hy : y < b) (hz : z < b)
    (hm : m < b) (hn : n < b)
    (hmx : m ≠ x) (hmy : m ≠ y) (hmz : m ≠ z)
    (hnx : n ≠ x) (hny : n ≠ y) (hnz : n ≠ z) (hmn : m ≠ n) :
    theoremCode (certificate (dynamic_exists b x y z m n hb hx hy hz hm hn
      hmx hmy hmz hnx hny hnz hmn)) =
      imp (domainAt b y).encode (imp (domainAt b z).encode
        (imp (addAt b x y z).encode (result b x y z m n).encode)) :=
  certificate_correct _

#print axioms dynamic_exists
#print axioms dynamic_exists_certificate
end PASoundness.PAtoCompactPAAddSuccDynamicWitness
