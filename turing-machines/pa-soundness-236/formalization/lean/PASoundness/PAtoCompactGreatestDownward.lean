import PASoundness.PAtoCompactPredecessor

/-! Syntactic K closure tools for the represented greatest-subset condition.
This does not assert that an arithmetic domain exists. Code 1 is literally
self-membership, so its ordinary falsity reading is model dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGreatestDownward
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactGreatestSuccessor
open PASoundness.PAtoCompactPredecessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- An arbitrary instance of the represented-subset formula. -/
def subset_instance (a b k v : Nat) (hkv : k ≠ v) (hka : k ≠ a) (hkb : k ≠ b) :
    KDerivation (imp (subsetCode a b k) (imp (member a v) (member b v))) := by
  let f : CompactNamed.Formula := .imp (.member a k) (.member b k)
  have h := CompactNamed.universalInstance k v f hkv
    (by simp [f, CompactNamed.Formula.binders])
    (by simp [f, CompactNamed.Formula.binders])
  simpa [f, subsetCode, CompactNamed.Formula.encode, CompactNamed.replace,
    CompactNamed.rename, hkv, hka, hkb, Ne.symm hkv, Ne.symm hka, Ne.symm hkb] using h

/-- The subset formula is vacuous at a fresh name. -/
def subset_vacuity (a b k v : Nat) (hva : v ≠ a) (hvb : v ≠ b) (hvk : v ≠ k) :
    KDerivation (imp (subsetCode a b k) (allCode v (subsetCode a b k))) := by
  let f : CompactNamed.Formula := .all k (.imp (.member a k) (.member b k))
  have hn : v ∉ f.names := by simp [f, CompactNamed.Formula.names, hva, hvb, hvk]
  have h := f.vacuity v hn
  simpa [f, subsetCode, CompactNamed.Formula.encode] using h

/-- Fresh quantifier labels give K-equivalent subset formulas. -/
def subset_rename (a b s k : Nat) (hsk : s ≠ k) (hsa : s ≠ a) (hsb : s ≠ b)
    (hka : k ≠ a) (hkb : k ≠ b) :
    KDerivation (imp (subsetCode a b s) (subsetCode a b k)) := by
  let f : CompactNamed.Formula := .imp (.member a s) (.member b s)
  have h := CompactNamed.universalAlpha s k f hsk
    (by simp [f, CompactNamed.Formula.binders])
    (by simp [f, CompactNamed.Formula.names, hka, hkb, Ne.symm hsk])
  simpa [f, subsetCode, CompactNamed.Formula.encode, CompactNamed.replace,
    CompactNamed.rename, hsk, hsa, hsb, hka, hkb, Ne.symm hsk, Ne.symm hsa,
    Ne.symm hsb, Ne.symm hka, Ne.symm hkb] using h.1

/-- Every represented subset of a represented subset is a subset of the outer
set. The four object/binder labels and temporary test name are pairwise fresh. -/
def subset_trans (x y r k s : Nat) (fresh : [x,y,r,k,s].Nodup) :
    KDerivation (imp (subsetCode y x k) (imp (subsetCode r y k) (subsetCode r x k))) := by
  have hsk : s ≠ k := by intro h; subst s; simp at fresh
  have hsx : s ≠ x := by intro h; subst s; simp at fresh
  have hsy : s ≠ y := by intro h; subst s; simp at fresh
  have hsr : s ≠ r := by intro h; subst s; simp at fresh
  have hkx : k ≠ x := by intro h; subst k; simp at fresh
  have hky : k ≠ y := by intro h; subst k; simp at fresh
  have hkr : k ≠ r := by intro h; subst k; simp at fresh
  let A := subsetCode y x k
  let B := subsetCode r y k
  let Γ := [B,A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (member r s) (member x s)) := by
    apply Context.deduction
    have hm : Context (member r s :: Γ) (member r s) := Context.head Γ _
    have hmy : Context (member r s :: Γ) (member y s) :=
      .mp hm (.mp (Context.under hb _) (.closed (subset_instance r y k s (Ne.symm hsk) hkr hky)))
    exact .mp hmy (.mp (Context.under ha _) (.closed (subset_instance y x k s (Ne.symm hsk) hky hkx)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode s h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = B
    · subst h
      exact subset_vacuity r y k s hsr hsy hsk
    · have he' : h = A := hh.resolve_left he
      subst h
      exact subset_vacuity y x k s hsy hsx hsk
  have hs : Context Γ (subsetCode r x s) := Context.generalize s hv hpoint
  have hout : Context Γ (subsetCode r x k) := .mp hs (.closed (subset_rename r x s k hsk hsr hsx hkr hkx))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

/-- Instantiate the greatest-subset condition at a named represented set. -/
def greatest_subsets_instance (x u k m t r : Nat)
    (hux : u ≠ x) (hur : u ≠ r) (huk : u ≠ k) (hum : u ≠ m) (hut : u ≠ t)
    (hrk : r ≠ k) (hrm : r ≠ m) (hrt : r ≠ t) :
    KDerivation (imp (greatestSubsetsCode x u k m t)
      (imp (subsetCode r x k) (imp (nonemptyCode r m) (hasGreatestCode r m t)))) := by
  let f := namedGreatestSubsetsBody x u k m t
  have hi := CompactNamed.universalInstance u r f hur
    (by simp [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      CompactNamed.Formula.binders, huk, hum, hut])
    (by simp [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      CompactNamed.Formula.binders, hrk, hrm, hrt])
  simpa [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
    greatestSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode, greatestCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hux, hur, huk, hum, hut, hrk, hrm, hrt, Ne.symm hux, Ne.symm hur,
    Ne.symm huk, Ne.symm hum, Ne.symm hut, Ne.symm hrk, Ne.symm hrm, Ne.symm hrt] using hi

/-- Vacuity of a greatest-subset hypothesis at a fresh name. -/
def greatest_subsets_vacuity (x u k m t r : Nat)
    (hrx : r ≠ x) (hru : r ≠ u) (hrk : r ≠ k) (hrm : r ≠ m) (hrt : r ≠ t) :
    KDerivation (imp (greatestSubsetsCode x u k m t)
      (allCode r (greatestSubsetsCode x u k m t))) := by
  let f : CompactNamed.Formula := .all u (namedGreatestSubsetsBody x u k m t)
  have hn : r ∉ f.names := by
    simp [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      CompactNamed.Formula.names, hrx, hru, hrk, hrm, hrt]
  have h := f.vacuity r hn
  simpa [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
    greatestSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode, greatestCode,
    CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
    CompactDerivations.either] using h

/-- K proves the greatest-subset condition descends to any represented subset.
The output condition uses a fresh outer subset binder r; all other displayed
names are retained. This is conditional on the input greatest-subset property. -/
def greatest_subsets_downward (x y u k m t r s : Nat)
    (fresh : [x,y,u,k,m,t,r,s].Nodup) :
    KDerivation (imp (greatestSubsetsCode x u k m t) (imp (subsetCode y x k)
      (greatestSubsetsCode y r k m t))) := by
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have hur : u ≠ r := by intro h; subst u; simp at fresh
  have huk : u ≠ k := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hut : u ≠ t := by intro h; subst u; simp at fresh
  have hrx : r ≠ x := by intro h; subst r; simp at fresh
  have hry : r ≠ y := by intro h; subst r; simp at fresh
  have hru : r ≠ u := by intro h; subst r; simp at fresh
  have hrk : r ≠ k := by intro h; subst r; simp at fresh
  have hrm : r ≠ m := by intro h; subst r; simp at fresh
  have hrt : r ≠ t := by intro h; subst r; simp at fresh
  have hf : [x,y,r,k,s].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  let G := greatestSubsetsCode x u k m t
  let A := subsetCode y x k
  let Γ := [A,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (subsetCode r y k)
      (imp (nonemptyCode r m) (hasGreatestCode r m t))) := by
    apply Context.deduction
    apply Context.deduction
    have hs : Context (nonemptyCode r m :: subsetCode r y k :: Γ) (subsetCode r y k) :=
      .hypothesis (by simp [Γ])
    have hn : Context (nonemptyCode r m :: subsetCode r y k :: Γ) (nonemptyCode r m) :=
      Context.head _ _
    have ha' := Context.under (Context.under ha (subsetCode r y k)) (nonemptyCode r m)
    have hg' := Context.under (Context.under hg (subsetCode r y k)) (nonemptyCode r m)
    have hsub : Context (nonemptyCode r m :: subsetCode r y k :: Γ) (subsetCode r x k) :=
      .mp hs (.mp ha' (.closed (subset_trans x y r k s hf)))
    exact .mp hn (.mp hsub (.mp hg' (.closed
      (greatest_subsets_instance x u k m t r hux hur huk hum hut hrk hrm hrt))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode r h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = A
    · subst h
      exact subset_vacuity y x k r hry hrx hrk
    · have he' : h = G := hh.resolve_left he
      subst h
      exact greatest_subsets_vacuity x u k m t r hrx hru hrk hrm hrt
  have hout : Context Γ (greatestSubsetsCode y r k m t) := Context.generalize r hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

theorem greatest_subsets_downward_certificate (x y u k m t r s : Nat)
    (fresh : [x,y,u,k,m,t,r,s].Nodup) :
    theoremCode (certificate (greatest_subsets_downward x y u k m t r s fresh)) =
      imp (greatestSubsetsCode x u k m t) (imp (subsetCode y x k)
        (greatestSubsetsCode y r k m t)) :=
  certificate_correct (greatest_subsets_downward x y u k m t r s fresh)

end PASoundness.PAtoCompactGreatestDownward

#print axioms PASoundness.PAtoCompactGreatestDownward.greatest_subsets_downward
#print axioms PASoundness.PAtoCompactGreatestDownward.greatest_subsets_downward_certificate
