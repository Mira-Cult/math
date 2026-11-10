import PASoundness.PAtoCompactSingleton
import PASoundness.PAtoCompactPairSelector

/-! Unordered pair representation in literal K. This is a finite syntactic
construction; it does not assume extensionality or uniqueness of the container. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactUnorderedPair
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactPairSelector

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def pairCode (a b s q : Nat) : Nat :=
  allCode q (both (imp (member s q) (either (equal q a) (equal q b)))
    (imp (either (equal q a) (equal q b)) (member s q)))

def namedPair (a b s q : Nat) : CompactNamed.Formula :=
  .all q (namedBoth (.imp (.member s q) (namedEither (.equal q a) (.equal q b)))
    (.imp (namedEither (.equal q a) (.equal q b)) (.member s q)))

/-- A singleton graph can be instantiated at any fresh test label. -/
def singleton_instance (a s q r : Nat) (hqa : q ≠ a) (hqs : q ≠ s) (hqr : q ≠ r) :
    KDerivation (imp (singletonCode a s q)
      (both (imp (member s r) (equal r a)) (imp (equal r a) (member s r)))) := by
  let f : CompactNamed.Formula := namedBoth (.imp (.member s q) (.equal q a))
    (.imp (.equal q a) (.member s q))
  have hi := CompactNamed.universalInstance q r f hqr
    (by simp [f, namedBoth, CompactNamed.Formula.binders])
    (by simp [f, namedBoth, CompactNamed.Formula.binders])
  simpa [f, namedBoth, singletonCode, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    hqa, hqs, hqr, Ne.symm hqa, Ne.symm hqs, Ne.symm hqr] using hi

def namedPairPredicate (a b t : Nat) : CompactNamed.Formula :=
  namedEither (.equal t a) (.equal t b)

def namedPairInner (s a b t : Nat) : CompactNamed.Formula :=
  let c := pairPredicate a b t
  namedBoth (.imp (.member s t) (.imp (namedPairPredicate a b t) (.member c t)))
    (.imp (.member c t) (namedPairPredicate a b t))

def namedPairSelectorBody (s a b t : Nat) : CompactNamed.Formula :=
  let c := pairPredicate a b t
  namedBoth (.all t (namedPairInner s a b t))
    (.imp (namedPairPredicate a b t) (.member c t))

/-- The selector's pair predicate can be instantiated without capture. -/
def pair_inner_instance (s a b t r : Nat)
    (hta : t ≠ a) (htb : t ≠ b) (hts : t ≠ s) (htr : t ≠ r) :
    KDerivation (imp (allCode t (namedPairInner s a b t).encode)
      (both (imp (member s r) (imp (pairPredicate a b r) (member (pairPredicate a b t) r)))
        (imp (member (pairPredicate a b t) r) (pairPredicate a b r)))) := by
  have hc := PAtoCompactPairSelector.predicate_names_lt a b t
  have htc : t ≠ pairPredicate a b t := by omega
  have hct : pairPredicate a b t ≠ t := by omega
  have hct' : imp (imp (equal t a) 1) (equal t b) ≠ t := hct
  have h := CompactNamed.universalInstance t r (namedPairInner s a b t) htr
    (by simp [namedPairInner, namedPairPredicate, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [namedPairInner, namedPairPredicate, namedBoth, namedEither, CompactNamed.Formula.binders])
  simpa [namedPairInner, namedPairPredicate, namedBoth, namedEither, pairPredicate,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hta, htb, hts, htr, htc, hct, hct', Ne.symm hta, Ne.symm htb,
    Ne.symm hts, Ne.symm htr, Ne.symm htc] using h

/-- With a singleton of a, the selector body and t=b give the intended pair
membership equivalence at the fresh test name r. -/
def pair_pointwise (s a b t q r : Nat) (fresh : [s,a,b,t,q,r].Nodup) :
    KDerivation (imp (singletonCode a s q) (imp (pairSelectorBody s a b t)
      (imp (equal t b)
        (both (imp (member (pairPredicate a b t) r) (pairPredicate a b r))
          (imp (pairPredicate a b r) (member (pairPredicate a b t) r)))))) := by
  have hta : t ≠ a := by intro h; subst t; simp at fresh
  have htb : t ≠ b := by intro h; subst t; simp at fresh
  have hts : t ≠ s := by intro h; subst t; simp at fresh
  have htr : t ≠ r := by intro h; subst t; simp at fresh
  have hqa : q ≠ a := by intro h; subst q; simp at fresh
  have hqs : q ≠ s := by intro h; subst q; simp at fresh
  have hqr : q ≠ r := by intro h; subst q; simp at fresh
  let c := pairPredicate a b t
  let P := pairPredicate a b r
  let S := singletonCode a s q
  let B := pairSelectorBody s a b t
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal t b,B,S]
  have he : Context Γ (equal t b) := .hypothesis (by simp [Γ])
  have hp : Context Γ B := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hbound : Context Γ (allCode t (namedPairInner s a b t).encode) := by
    have hh := Context.conjunctionLeft hp
    simpa [B, pairSelectorBody, pairPredicate, namedPairInner, namedPairPredicate, namedBoth, namedEither,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hh
  have hi := Context.mp hbound (.closed (pair_inner_instance s a b t r hta htb hts htr))
  have hforward : Context Γ (imp (member c r) P) := Context.conjunctionRight hi
  have hpositive : Context Γ (imp (member s r) (imp P (member c r))) := Context.conjunctionLeft hi
  have hsr : Context Γ (imp (equal r a) (member s r)) :=
    Context.conjunctionRight (.mp hs (.closed (singleton_instance a s q r hqa hqs hqr)))
  have hcb : Context Γ (member c b) := by
    have houter : Context Γ (imp c (member c t)) := Context.conjunctionRight hp
    have hpred : Context Γ c := Context.disjunctionRight (a := equal t a) he
    exact .mp he (.mp (.mp hpred houter) (.closed (memberRightEquality c t b)))
  have hreverse : Context Γ (imp P (member c r)) := by
    apply Context.deduction
    have hP : Context (P :: Γ) P := Context.head Γ P
    apply Context.disjunctionElim hP
    · have ha : Context (equal r a :: P :: Γ) (equal r a) := Context.head _ _
      have hm : Context (equal r a :: P :: Γ) (member s r) :=
        .mp ha (Context.under (Context.under hsr P) _)
      exact .mp (Context.under (Context.head Γ P) _) (.mp hm (Context.under (Context.under hpositive P) _))
    · have hb : Context (equal r b :: P :: Γ) (equal r b) := Context.head _ _
      have hm : Context (equal r b :: P :: Γ) (member c b) :=
        Context.under (Context.under hcb P) _
      exact .mp (Context.eqSymm hb) (.mp hm (.closed (memberRightEquality c b r)))
  exact Context.conjunctionIntro hforward hreverse

/-- With explicit freshness, the supplied selector body, singleton graph and
point equality derive the complete unordered-pair graph. -/
def pair_body_graph (s a b t q r : Nat) (fresh : [s,a,b,t,q,r].Nodup)
    (hrc : r ≠ pairPredicate a b t) :
    KDerivation (imp (singletonCode a s q) (imp (pairSelectorBody s a b t)
      (imp (equal t b) (pairCode a b (pairPredicate a b t) r)))) := by
  have hrs : r ≠ s := by intro h; subst r; simp at fresh
  have hra : r ≠ a := by intro h; subst r; simp at fresh
  have hrb : r ≠ b := by intro h; subst r; simp at fresh
  have hrt : r ≠ t := by intro h; subst r; simp at fresh
  have hrq : r ≠ q := by intro h; subst r; simp at fresh
  let S := singletonCode a s q
  let B := pairSelectorBody s a b t
  let E := equal t b
  let c := pairPredicate a b t
  let Γ := [E,B,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (both (imp (member c r) (pairPredicate a b r))
      (imp (pairPredicate a b r) (member c r))) :=
    .mp he (.mp hb (.mp hs (.closed (pair_pointwise s a b t q r fresh))))
  let fS := namedSingleton a s q
  have hnamesS : r ∉ fS.names := by
    simp [fS, namedSingleton, namedBoth, CompactNamed.Formula.names, hrs, hra, hrq]
  have hvS : KDerivation (imp S (allCode r S)) := by
    have h := fS.vacuity r hnamesS
    simpa [fS, S, namedSingleton, namedBoth, singletonCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg] using h
  let fB := namedPairSelectorBody s a b t
  have hnamesB : r ∉ fB.names := by
    simp [fB, namedPairSelectorBody, namedPairInner, namedPairPredicate, namedBoth, namedEither,
      CompactNamed.Formula.names, hrs, hra, hrb, hrt, hrc]
  have hvB : KDerivation (imp B (allCode r B)) := by
    have h := fB.vacuity r hnamesB
    simpa [fB, B, namedPairSelectorBody, namedPairInner, namedPairPredicate, namedBoth, namedEither,
      pairSelectorBody, pairPredicate, CompactNamed.Formula.encode,
      CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  have hvE : KDerivation (imp E (allCode r E)) := equalityVacuity t b r hrt hrb
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode r h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he' : h = E
    · subst h; exact hvE
    · by_cases hb' : h = B
      · subst h; exact hvB
      · have hs' : h = S := (hh.resolve_left he').resolve_left hb'
        subst h; exact hvS
  have hg : Context Γ (pairCode a b c r) := by
    have h := Context.generalize r hv hpoint
    simpa [pairCode, pairPredicate] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hg

theorem pair_body_graph_certificate (s a b t q r : Nat) (fresh : [s,a,b,t,q,r].Nodup)
    (hrc : r ≠ pairPredicate a b t) :
    theoremCode (certificate (pair_body_graph s a b t q r fresh hrc)) =
      imp (singletonCode a s q) (imp (pairSelectorBody s a b t)
        (imp (equal t b) (pairCode a b (pairPredicate a b t) r))) :=
  certificate_correct (pair_body_graph s a b t q r fresh hrc)

end PASoundness.PAtoCompactUnorderedPair

#print axioms PASoundness.PAtoCompactUnorderedPair.pair_body_graph
#print axioms PASoundness.PAtoCompactUnorderedPair.pair_body_graph_certificate
