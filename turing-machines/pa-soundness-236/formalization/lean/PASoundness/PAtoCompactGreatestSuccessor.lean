import PASoundness.PAtoCompactTransitiveClosure

/-! Greatest-member-to-successor graph, as a finite syntactic K derivation.
No predecessor existence, domain closure or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGreatestSuccessor
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure

/-- Every element of x is either m or an element of m. The separate hypothesis
`member x m` says m itself is a member of x. -/
def greatestCode (x m t : Nat) : Nat :=
  allCode t (imp (member x t) (either (equal t m) (member m t)))

def namedGreatestBody (x m t : Nat) : CompactNamed.Formula :=
  .imp (.member x t) (namedEither (.equal t m) (.member m t))

/-- Fresh variable instantiation of the greatest-member condition. -/
def greatest_instance (x m t r : Nat) (htx : t ≠ x) (htm : t ≠ m) (htr : t ≠ r) :
    KDerivation (imp (greatestCode x m t)
      (imp (member x r) (either (equal r m) (member m r)))) := by
  have h := CompactNamed.universalInstance t r (namedGreatestBody x m t) htr
    (by simp [namedGreatestBody, namedEither, CompactNamed.Formula.binders])
    (by simp [namedGreatestBody, namedEither, CompactNamed.Formula.binders])
  simpa [greatestCode, namedGreatestBody, namedEither, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.neg, CompactDerivations.either,
    htx, htm, htr, Ne.symm htx, Ne.symm htm, Ne.symm htr] using h

/-- Fresh-name vacuity for the greatest-member condition. -/
def greatest_vacuity (x m t r : Nat) (hrx : r ≠ x) (hrm : r ≠ m) (hrt : r ≠ t) :
    KDerivation (imp (greatestCode x m t) (allCode r (greatestCode x m t))) := by
  let f : CompactNamed.Formula := .all t (namedGreatestBody x m t)
  have hf : r ∉ f.names := by
    simp [f, namedGreatestBody, namedEither, CompactNamed.Formula.names, hrx, hrm, hrt]
  have h := f.vacuity r hf
  simpa [f, greatestCode, namedGreatestBody, namedEither, CompactNamed.Formula.encode,
    CompactProof.neg, CompactDerivations.either] using h

/-- A greatest member m of a transitive set x is a predecessor: the exact
successor graph of m and x is derivable in K. The extra test names in the
transitivity and greatest formulas, as well as graph test r, are explicit. -/
def greatest_member_successor (x m p q t r : Nat)
    (hpx : p ≠ x) (hpm : p ≠ m) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqm : q ≠ m) (hqr : q ≠ r)
    (htx : t ≠ x) (htm : t ≠ m) (htr : t ≠ r)
    (hrx : r ≠ x) (hrm : r ≠ m) (hrp : r ≠ p) (hrq : r ≠ q) (hrt : r ≠ t) :
    KDerivation (imp (transitiveCode x p q) (imp (member x m)
      (imp (greatestCode x m t) (successorCode m x r)))) := by
  let T := transitiveCode x p q
  let G := greatestCode x m t
  let Γ := [G, member x m, T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hm : Context Γ (member x m) := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hfwd : Context Γ (imp (member x r) (either (equal r m) (member m r))) :=
    .mp hg (.closed (greatest_instance x m t r htx htm htr))
  have hback : Context Γ (imp (either (equal r m) (member m r)) (member x r)) := by
    apply Context.deduction
    have hp : Context (either (equal r m) (member m r) :: Γ)
        (either (equal r m) (member m r)) := Context.head Γ _
    apply Context.disjunctionElim hp
    · have he : Context (equal r m :: either (equal r m) (member m r) :: Γ) (equal r m) :=
        Context.head _ _
      have hm' : Context (equal r m :: either (equal r m) (member m r) :: Γ) (member x m) :=
        Context.under (Context.under hm _) _
      exact .mp (Context.eqSymm he) (.mp hm' (.closed (memberRightEquality x m r)))
    · have hr : Context (member m r :: either (equal r m) (member m r) :: Γ) (member m r) :=
        Context.head _ _
      have hm' : Context (member m r :: either (equal r m) (member m r) :: Γ) (member x m) :=
        Context.under (Context.under hm _) _
      have ht' : Context (member m r :: either (equal r m) (member m r) :: Γ) T :=
        Context.under (Context.under ht _) _
      exact .mp hr (.mp hm' (.mp ht' (.closed (transitive_chain x p q m r hpx hpm hpq hqx hqm hqr))))
  have hpoint : Context Γ (both (imp (member x r) (either (equal r m) (member m r)))
      (imp (either (equal r m) (member m r)) (member x r))) :=
    Context.conjunctionIntro hfwd hback
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode r h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = G
    · subst h
      exact greatest_vacuity x m t r hrx hrm hrt
    · by_cases h2 : h = member x m
      · subst h
        exact membershipVacuity x m r hrx hrm
      · have h3 : h = T := (hh.resolve_left h1).resolve_left h2
        subst h
        exact transitive_vacuity x p q r hrx hrp hrq
  have hgraph : Context Γ (successorCode m x r) := Context.generalize r hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hgraph

theorem greatest_member_successor_certificate (x m p q t r : Nat)
    (hpx : p ≠ x) (hpm : p ≠ m) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqm : q ≠ m) (hqr : q ≠ r)
    (htx : t ≠ x) (htm : t ≠ m) (htr : t ≠ r)
    (hrx : r ≠ x) (hrm : r ≠ m) (hrp : r ≠ p) (hrq : r ≠ q) (hrt : r ≠ t) :
    theoremCode (certificate (greatest_member_successor x m p q t r hpx hpm hpq hqx hqm hqr
      htx htm htr hrx hrm hrp hrq hrt)) =
      imp (transitiveCode x p q) (imp (member x m)
        (imp (greatestCode x m t) (successorCode m x r))) :=
  certificate_correct (greatest_member_successor x m p q t r hpx hpm hpq hqx hqm hqr
    htx htm htr hrx hrm hrp hrq hrt)

/-- Exact standard HF-code meaning of the greatest-member formula. This is a
semantic lemma, separate from the constructive K derivation above. -/
theorem greatestCode_realize (x m t : Nat) (ρ : CompactMatrix.Environment)
    (hxt : x ≠ t) (hmt : m ≠ t) :
    (CompactMatrix.decode (greatestCode x m t)).Realize ρ ↔
      ∀ v, CompactMatrix.bit (ρ x) v = true →
        (v = ρ m ∨ CompactMatrix.bit (ρ m) v = true) := by
  simp only [greatestCode, CompactSemantics.realize_all, CompactSemantics.realize_imp,
    CompactDerivations.either, CompactSemantics.realize_neg, CompactSemantics.realize_equal,
    CompactSemantics.realize_member]
  simp only [CompactSemantics.update_same, CompactSemantics.update_other ρ t x _ hxt,
    CompactSemantics.update_other ρ t m _ hmt]
  apply forall_congr'
  intro v
  classical
  tauto

/-- Each positive finite ordinal has its immediate predecessor as greatest
member, in the standard HF-code interpretation. -/
theorem ordinal_predecessor_greatest (x m t n : Nat) (ρ : CompactMatrix.Environment)
    (hxt : x ≠ t) (hmt : m ≠ t)
    (hx : ρ x = (HFCoding.ordinal (n+1)).code)
    (hm : ρ m = (HFCoding.ordinal n).code) :
    (CompactMatrix.decode (greatestCode x m t)).Realize ρ := by
  rw [greatestCode_realize x m t ρ hxt hmt]
  intro v hv
  have hv' : (⟨v⟩ : HFCoding.Object) ∈ HFCoding.successor (HFCoding.ordinal n) := by
    change CompactMatrix.bit (HFCoding.successor (HFCoding.ordinal n)).code v = true
    simpa [hx, HFCoding.ordinal] using hv
  rw [HFCoding.mem_successor] at hv'
  rcases hv' with he | he
  · left
    have hh := congrArg HFCoding.Object.code he
    simpa [hm] using hh
  · right
    change CompactMatrix.bit (HFCoding.ordinal n).code v = true at he
    simpa [hm] using he

end PASoundness.PAtoCompactGreatestSuccessor
