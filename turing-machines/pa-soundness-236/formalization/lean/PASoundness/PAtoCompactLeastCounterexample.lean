import PASoundness.PAtoCompactCounterexampleSet
import PASoundness.PAtoCompactPredecessor

/-! Conditional K construction of a least counterexample in an explicit
filtered graph. The least-element property is an antecedent, not a theorem.
Compact conjunction/existence/negation use literal code 1 = `member 0 0`;
their ordinary logical reading is separate from arbitrary raw K models. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastCounterexample
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactGreatestSuccessor
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactCounterexampleSet

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- m is a member of u and every member v of u is equal to m or contains m.
The membership order is explicit: `member v m` means m∈v. -/
def leastMemberCode (u m r : Nat) : Nat :=
  both (member u m) (allCode r (imp (member u r) (either (equal r m) (member r m))))

/-- Every nonempty represented subset of x has an actual least member under
membership. This is an assumption, not an asserted K theorem. -/
def leastSubsetsCode (x u k a m r : Nat) : Nat :=
  allCode u (imp (subsetCode u x k) (imp (nonemptyCode u a)
    (existsCode m (leastMemberCode u m r))))

def namedLeastMember (u m r : Nat) : CompactNamed.Formula :=
  namedBoth (.member u m)
    (.all r (.imp (.member u r) (namedEither (.equal r m) (.member r m))))

def namedLeastSubsetsBody (x u k a m r : Nat) : CompactNamed.Formula :=
  .imp (.all k (.imp (.member u k) (.member x k)))
    (.imp (.ex a (.member u a)) (.ex m (namedLeastMember u m r)))

/-- A filtered graph is a represented subset of x, using only K projections. -/
def filter_graph_subset (x y t P : Nat) :
    KDerivation (imp (filterGraph x y t P) (subsetCode y x t)) := by
  let W := member y t
  let A := member x t
  let F := filterPredicate x t P
  let I := both (imp W F) (imp F W)
  have hinner : KDerivation (imp I (imp W A)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have hw : Context [W,I] W := Context.head [I] W
    have hi : Context [W,I] I := Context.under (Context.head [] I) W
    have hf : Context [W,I] F := .mp hw (Context.conjunctionLeft hi)
    exact Context.conjunctionLeft hf
  exact allCongr t hinner

/-- Instantiation of the least-subset property at a named represented set. -/
def least_subsets_instance (x u k a m r y : Nat)
    (hux : u ≠ x) (huy : u ≠ y)
    (huk : u ≠ k) (hua : u ≠ a) (hum : u ≠ m) (hur : u ≠ r)
    (hyk : y ≠ k) (hya : y ≠ a) (hym : y ≠ m) (hyr : y ≠ r) :
    KDerivation (imp (leastSubsetsCode x u k a m r)
      (imp (subsetCode y x k) (imp (nonemptyCode y a) (existsCode m (leastMemberCode y m r))))) := by
  let f := namedLeastSubsetsBody x u k a m r
  have hi := CompactNamed.universalInstance u y f huy
    (by simp [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
      CompactNamed.Formula.binders, huk, hua, hum, hur])
    (by simp [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
      CompactNamed.Formula.binders, hyk, hya, hym, hyr])
  simpa [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
    leastSubsetsCode, leastMemberCode, subsetCode, nonemptyCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hux, huy, huk, hua, hum, hur, hyk, hya, hym, hyr,
    Ne.symm hux, Ne.symm huy, Ne.symm huk, Ne.symm hua, Ne.symm hum, Ne.symm hur,
    Ne.symm hyk, Ne.symm hya, Ne.symm hym, Ne.symm hyr] using hi

/-- Vacuity of the explicit least-subset hypothesis at a name absent from
all its free and bound names. -/
def least_subsets_vacuity (x u k a m r c : Nat)
    (hcx : c ≠ x) (hcu : c ≠ u) (hck : c ≠ k)
    (hca : c ≠ a) (hcm : c ≠ m) (hcr : c ≠ r) :
    KDerivation (imp (leastSubsetsCode x u k a m r)
      (allCode c (leastSubsetsCode x u k a m r))) := by
  let f : CompactNamed.Formula := .all u (namedLeastSubsetsBody x u k a m r)
  have hf : c ∉ f.names := by
    simp [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
      CompactNamed.Formula.names, hcx, hcu, hck, hca, hcm, hcr]
  have h := f.vacuity c hf
  simpa [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
    leastSubsetsCode, leastMemberCode, subsetCode, nonemptyCode,
    CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- Given an object-level least-subset hypothesis and an explicit counterexample,
K constructs a represented filtered set with an actual least member. The
conclusion retains the exact filter graph, so that member is a least
counterexample in the displayed membership order. All named assumptions and
binder-collision conditions remain explicit. -/
def least_counterexample_exists (x t a u m r : Nat) (f : CompactNamed.Formula)
    (fresh : [x,t,a,u,m,r].Nodup)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names) :
    let c := filterPredicate x t (neg f.encode)
    let inst := (CompactNamed.replace t a f).encode
    KDerivation (imp (leastSubsetsCode x u t a m r)
      (imp (member x a) (imp (neg inst)
        (existsCode c (both (filterGraph x c t (neg f.encode))
          (existsCode m (leastMemberCode c m r))))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let inst := (CompactNamed.replace t a f).encode
  have hxt : x ≠ t := by intro h; subst t; simp at fresh
  have hta : t ≠ a := by intro h; subst t; simp at fresh
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have hut : u ≠ t := by intro h; subst u; simp at fresh
  have hua : u ≠ a := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hur : u ≠ r := by intro h; subst u; simp at fresh
  have hc := filterPredicate_bounds x t (neg f.encode)
  have hcx : c ≠ x := by dsimp [c]; omega
  have hct : c ≠ t := by dsimp [c]; omega
  have hca : c ≠ a := by intro h; apply hcOthers; simp [c, h]
  have hcu : c ≠ u := by intro h; apply hcOthers; simp [c, h]
  have hcm : c ≠ m := by intro h; apply hcOthers; simp [c, h]
  have hcr : c ≠ r := by intro h; apply hcOthers; simp [c, h]
  let L := leastSubsetsCode x u t a m r
  let X := member x a
  let N := neg inst
  let G := filterGraph x c t (neg f.encode)
  let A := both G (nonemptyCode c a)
  let B := both G (existsCode m (leastMemberCode c m r))
  let Γ := [L]
  have hL : Context Γ L := Context.head [] L
  have hstep : Context Γ (imp A B) := by
    apply Context.deduction
    have ha : Context (A :: Γ) A := Context.head Γ A
    have hg : Context (A :: Γ) G := Context.conjunctionLeft ha
    have hn : Context (A :: Γ) (nonemptyCode c a) := Context.conjunctionRight ha
    have hsub : Context (A :: Γ) (subsetCode c x t) := .mp hg (.closed (filter_graph_subset x c t (neg f.encode)))
    have hprop : Context (A :: Γ)
        (imp (subsetCode c x t) (imp (nonemptyCode c a) (existsCode m (leastMemberCode c m r)))) :=
      .mp (Context.under hL A) (.closed (least_subsets_instance x u t a m r c
        hux (Ne.symm hcu) hut hua hum hur hct hca hcm hcr))
    have hleast : Context (A :: Γ) (existsCode m (leastMemberCode c m r)) :=
      .mp hn (.mp hsub hprop)
    exact Context.conjunctionIntro hg hleast
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode c h)) := by
    intro h hh
    have he : h = L := by simpa [Γ] using hh
    subst h
    exact least_subsets_vacuity x u t a m r c hcx hcu hct hca hcm hcr
  have hall : Context Γ (allCode c (imp A B)) := Context.generalize c hv hstep
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [N, X, L]
  have hX : Context Δ X := .hypothesis (by simp [Δ])
  have hN : Context Δ N := .hypothesis (by simp [Δ])
  have hex : Context Δ (existsCode c A) :=
    .mp hN (.mp hX (.closed (nonempty_counterexample_filter x t a f hxt hta htf haf hca hcf)))
  have hall' : Context Δ (allCode c (imp A B)) := Context.weaken hall (by
    intro h hh
    have he : h = L := by simpa [Γ] using hh
    subst h
    simp [Δ])
  exact exists_map_context hall' hex

theorem least_counterexample_certificate (x t a u m r : Nat) (f : CompactNamed.Formula)
    (fresh : [x,t,a,u,m,r].Nodup)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names) :
    let c := filterPredicate x t (neg f.encode)
    let inst := (CompactNamed.replace t a f).encode
    theoremCode (certificate (least_counterexample_exists x t a u m r f fresh htf haf hcOthers hcf)) =
      imp (leastSubsetsCode x u t a m r)
        (imp (member x a) (imp (neg inst)
          (existsCode c (both (filterGraph x c t (neg f.encode))
            (existsCode m (leastMemberCode c m r)))))) :=
  certificate_correct (least_counterexample_exists x t a u m r f fresh htf haf hcOthers hcf)

/-- Standard-HF reading of the displayed least-member code. -/
theorem leastMember_standard (u m r : Nat) (ρ : CompactMatrix.Environment)
    (hur : u ≠ r) (hmr : m ≠ r) :
    (CompactMatrix.decode (leastMemberCode u m r)).Realize ρ ↔
      (CompactMatrix.bit (ρ u) (ρ m) = true ∧
        ∀ v, CompactMatrix.bit (ρ u) v = true →
          (v = ρ m ∨ CompactMatrix.bit v (ρ m) = true)) := by
  simp only [leastMemberCode, CompactSemantics.realize_both, CompactSemantics.realize_member,
    CompactSemantics.realize_all, CompactSemantics.realize_imp, CompactDerivations.either,
    CompactSemantics.realize_neg, CompactSemantics.realize_equal]
  simp only [CompactSemantics.update_same, CompactSemantics.update_other ρ r u _ hur,
    CompactSemantics.update_other ρ r m _ hmr]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro v
  classical
  tauto

/-- A least member of an exact counterexample filter is a counterexample in x
and is below every member of that filter. This is the standard-HF semantic
reading of the K theorem's conclusion, not a premise used in its construction. -/
theorem standard_least_counterexample (x c t m r : Nat) (f : CompactNamed.Formula)
    (ρ : CompactMatrix.Environment) (hxt : x ≠ t) (hct : c ≠ t)
    (hcr : c ≠ r) (hmr : m ≠ r)
    (hg : (CompactMatrix.decode (filterGraph x c t (neg f.encode))).Realize ρ)
    (hl : (CompactMatrix.decode (leastMemberCode c m r)).Realize ρ) :
    CompactMatrix.bit (ρ x) (ρ m) = true ∧
      ¬ f.Realize (CompactMatrix.update ρ t (ρ m)) ∧
      ∀ v, CompactMatrix.bit (ρ c) v = true →
        (v = ρ m ∨ CompactMatrix.bit v (ρ m) = true) := by
  have hleast := (leastMember_standard c m r ρ hcr hmr).mp hl
  have hfilter := (filterGraph_standard x c t (neg f.encode) ρ hxt hct).mp hg
  have hcounter := (hfilter (ρ m)).mp hleast.1
  refine ⟨hcounter.1, ?_, hleast.2⟩
  simpa only [CompactSemantics.realize_neg, CompactNamed.Formula.encode_realize] using hcounter.2

end PASoundness.PAtoCompactLeastCounterexample
