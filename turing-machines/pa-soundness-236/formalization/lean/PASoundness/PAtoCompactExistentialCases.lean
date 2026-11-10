import PASoundness.PAtoCompactInductionCases

/-! A local K zero-or-existential-predecessor case proof. This is not a
quantified induction theorem or construction of an arithmetic domain. Code 1
is literally `member 0 0`; its ordinary falsity reading is model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactExistentialCases
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactCounterexampleSet
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactLeastZero
open PASoundness.PAtoCompactLeastPredecessor

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A predecessor branch explicitly carries domain membership, the successor
graph, transitivity of m, and the local predicate-preservation implication. -/
def predecessorBranch (x t y m w p q : Nat) (f : CompactNamed.Formula) : Nat :=
  let fy := (CompactNamed.replace t y f).encode
  let fm := (CompactNamed.replace t m f).encode
  both (member x y) (both (successorCode y m w)
    (both (transitiveCode m p q) (imp fy fm)))

/-- The object-level classification is zero or an existential predecessor
satisfying the displayed branch conditions. It is an antecedent, not proved. -/
def zeroOrExistentialPredecessor (x t y m z w p q : Nat) (f : CompactNamed.Formula) : Nat :=
  either (zeroCode m z) (existsCode y (predecessorBranch x t y m w p q f))

/-- Capture-safe existential lifting of the already checked zero and named
predecessor cases. The computed filter label c and original predicate names
are kept distinct from y; every remaining graph/binder condition is explicit.
The result concludes literal code 1 and does not assert a global schema. -/
def existential_predecessor_cases (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fm := (CompactNamed.replace t m f).encode
    KDerivation (imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
      (imp (zeroOrExistentialPredecessor x t y m z w p q f)
        (imp (imp (zeroCode m z) fm) 1)))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let Z := zeroCode m z
  let B := imp Z fm
  let D := predecessorBranch x t y m w p q f
  let C := zeroOrExistentialPredecessor x t y m z w p q f
  let Γ := [B,L,G]
  have hyb : y ∉ f.binders := fun h => hyf (f.binders_subset_names h)
  have hGraphNames : y ∉ (CompactNamed.Formula.all t (namedCounterexampleGraphBody x t f)).names := by
    simp [namedCounterexampleGraphBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.names, Ne.symm hty, hyc, hyx, hyf]
  have hvG : KDerivation (imp G (allCode y G)) := by
    have h := (CompactNamed.Formula.all t (namedCounterexampleGraphBody x t f)).vacuity y hGraphNames
    simpa [G, c, namedCounterexampleGraphBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, filterGraph, filterPredicate,
      CompactProof.both, CompactProof.neg] using h
  have hyc' : y ≠ c := hyc
  have hLeastNames : y ∉ (namedLeastMember c m r).names := by
    simp [namedLeastMember, namedBoth, namedEither, CompactNamed.Formula.names,
      hyc', hym, Ne.symm hry]
  have hvL : KDerivation (imp L (allCode y L)) := by
    have h := (namedLeastMember c m r).vacuity y hLeastNames
    simpa [L, namedLeastMember, namedBoth, namedEither, CompactNamed.Formula.encode,
      leastMemberCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  have hyReplace : y ∉ (CompactNamed.replace t m f).names := by
    intro hm
    have he := CompactNamed.replace_names_outside t m y f (Ne.symm hty) hym
    exact hyf (he.mp hm)
  let fBase : CompactNamed.Formula :=
    .imp (.all z (.imp (.member m z) .bottom)) (CompactNamed.replace t m f)
  have hBaseNames : y ∉ fBase.names := by
    simp [fBase, CompactNamed.Formula.names, hym, hyz, hyReplace]
  have hvB : KDerivation (imp B (allCode y B)) := by
    have h := fBase.vacuity y hBaseNames
    simpa [fBase, B, Z, fm, zeroCode, CompactNamed.Formula.encode, CompactProof.neg] using h
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode y h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = B
    · subst h
      exact hvB
    · by_cases h2 : h = L
      · subst h
        exact hvL
      · have h3 : h = G := (hh.resolve_left h1).resolve_left h2
        subst h
        exact hvG
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hL : Context Γ L := .hypothesis (by simp [Γ])
  have hB : Context Γ B := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp D 1) := by
    apply Context.deduction
    have hd : Context (D :: Γ) D := Context.head Γ D
    have hx : Context (D :: Γ) (member x y) := Context.conjunctionLeft hd
    have hrest := Context.conjunctionRight hd
    have hs : Context (D :: Γ) (successorCode y m w) := Context.conjunctionLeft hrest
    have htt := Context.conjunctionRight hrest
    have ht : Context (D :: Γ) (transitiveCode m p q) := Context.conjunctionLeft htt
    have hh : Context (D :: Γ) (imp (CompactNamed.replace t y f).encode fm) := Context.conjunctionRight htt
    exact .mp hh (.mp ht (.mp hs (.mp hx (.mp (Context.under hL D) (.mp (Context.under hG D)
      (.closed (least_predecessor_contradiction_transitive x t y m r w p q f
        hxt hty htm htf hyb hmf hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)))))))
  have hall : Context Γ (allCode y (neg D)) := Context.generalize y hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [B,C,L,G]
  have hg : Context Δ G := .hypothesis (by simp [Δ])
  have hl : Context Δ L := .hypothesis (by simp [Δ])
  have hc : Context Δ C := .hypothesis (by simp [Δ])
  have hb : Context Δ B := .hypothesis (by simp [Δ])
  change Context Δ (either Z (existsCode y D)) at hc
  apply Context.disjunctionElim hc
  · have hz : Context (Z :: Δ) Z := Context.head Δ Z
    exact .mp (Context.under hb Z) (.mp hz (.mp (Context.under hl Z)
      (.mp (Context.under hg Z) (.closed (least_zero_contradiction x t m r z f hxt htm hzm htf hmf)))))
  · have hex : Context (existsCode y D :: Δ) (existsCode y D) := Context.head Δ _
    have hall' : Context (existsCode y D :: Δ) (allCode y (neg D)) := Context.weaken hall (by
      intro h hh
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl <;> simp [Δ])
    exact .mp hall' hex

theorem existential_predecessor_cases_certificate (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fm := (CompactNamed.replace t m f).encode
    theoremCode (certificate (existential_predecessor_cases x t y m r z w p q f hxt hty htm hzm
      htf hmf hyf hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)) =
      imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
        (imp (zeroOrExistentialPredecessor x t y m z w p q f)
          (imp (imp (zeroCode m z) fm) 1))) :=
  certificate_correct (existential_predecessor_cases x t y m r z w p q f hxt hty htm hzm
    htf hmf hyf hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)

end PASoundness.PAtoCompactExistentialCases
