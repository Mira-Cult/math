import PASoundness.PAtoCompactOrdinalInterval
import PASoundness.PAtoCompactOrderedPairInjectivity
import PASoundness.PAtoCompactStandardReflexivity

/-! An explicit standard-HF graph for shifting a finite ordinal onto an
ordinal interval. This is a truth-side witness, not a K graph-existence or
quotient theorem. -/
namespace PASoundness.PAtoCompactOrdinalShiftGraph
open PASoundness.HFCoding PASoundness.PAtoCompactOrderedPair
open PASoundness.PAtoCompactOrderedPairInjectivity
open PASoundness.PAtoCompactOrdinalInterval PASoundness.PAtoCompactGraphMeaning
open PASoundness.CompactMatrix (Environment bit update)
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactBijectionMeaning PASoundness.PAtoCompactOrderMeaning

/-- The represented graph of `r ↦ l+r` for indices `r<n`. -/
def shiftGraph (l n : Nat) : Object :=
  assemble ((Finset.range n).image (fun r => orderedPair (ordinal r) (ordinal (l+r))))

/-- Exact edge relation of the represented shift graph. -/
theorem shift_graphRel (l n a b : Nat) :
    graphRel (shiftGraph l n).code a b ↔
      ∃ r, r<n ∧ a=(ordinal r).code ∧ b=(ordinal (l+r)).code := by
  classical
  change orderedPair ⟨a⟩ ⟨b⟩ ∈ shiftGraph l n ↔ _
  simp only [shiftGraph, mem_assemble, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨r, hr, he⟩
    obtain ⟨ha,hb⟩ := orderedPair_injective (ordinal r) (ordinal (l+r)) ⟨a⟩ ⟨b⟩ he
    exact ⟨r,hr,(congrArg Object.code ha).symm,(congrArg Object.code hb).symm⟩
  · rintro ⟨r,hr,ha,hb⟩
    refine ⟨r,hr,?_⟩
    apply congrArg₂ orderedPair
    · exact code_injective ha.symm
    · exact code_injective hb.symm

/-- Every member of the interval is uniquely reached by the shift. -/
theorem interval_shift_edge (l n b : Nat) :
    bit (ordinalInterval l (l+n)).code b = true ↔
      ∃ a, bit (ordinal n).code a = true ∧ graphRel (shiftGraph l n).code a b := by
  constructor
  · intro hb
    have hb' : (⟨b⟩ : Object) ∈ ordinalInterval l (l+n) := hb
    obtain ⟨k,hlo,hhi,hk⟩ := (mem_interval _ _ _).mp hb'
    let r := k-l
    have hr : r<n := by dsimp [r]; omega
    have hrk : l+r=k := by dsimp [r]; omega
    refine ⟨(ordinal r).code, ordinal_member hr, ?_⟩
    apply (shift_graphRel l n _ _).mpr
    refine ⟨r,hr,rfl,?_⟩
    simpa [hrk] using congrArg Object.code hk
  · rintro ⟨a,ha,hg⟩
    obtain ⟨r,hr,_,hb⟩ := (shift_graphRel l n a b).mp hg
    have hmem : ordinal (l+r) ∈ ordinalInterval l (l+n) :=
      (mem_interval _ _ _).mpr ⟨l+r,by omega,by omega,rfl⟩
    change bit (ordinalInterval l (l+n)).code (ordinal (l+r)).code = true at hmem
    change bit (ordinalInterval l (l+n)).code b = true
    simpa [hb] using hmem

/-- The concrete candidate isomorphism relates ordinal `n` to the interval
`[l,l+n)` in standard HF, witnessed by the explicitly assembled shift graph. -/
theorem standard_shift_equivalent (ρ : Environment) (l n : Nat)
    (h0 : ρ 0 = (ordinal n).code)
    (h1 : ρ 1 = (ordinalInterval l (l+n)).code) :
    equivalentFormula.Realize ρ := by
  classical
  let G := (shiftGraph l n).code
  let η := update ρ 6 G
  have hg23 : ∀ σ, (graphFormula 6 2 3).Realize σ ↔ graphRel (σ 6) (σ 2) (σ 3) := by
    intro σ; exact graphFormula_realize_iff 6 2 3 σ (by decide) (by decide) (by decide)
  have hg24 : ∀ σ, (graphFormula 6 2 4).Realize σ ↔ graphRel (σ 6) (σ 2) (σ 4) := by
    intro σ; exact graphFormula_realize_iff 6 2 4 σ (by decide) (by decide) (by decide)
  have hg43 : ∀ σ, (graphFormula 6 4 3).Realize σ ↔ graphRel (σ 6) (σ 4) (σ 3) := by
    intro σ; exact graphFormula_realize_iff 6 4 3 σ (by decide) (by decide) (by decide)
  have hg45 : ∀ σ, (graphFormula 6 4 5).Realize σ ↔ graphRel (σ 6) (σ 4) (σ 5) := by
    intro σ; exact graphFormula_realize_iff 6 4 5 σ (by decide) (by decide) (by decide)
  have hv0 : η 0 = (ordinal n).code := by simp [η, h0]
  have hv1 : η 1 = (ordinalInterval l (l+n)).code := by simp [η, h1]
  have hv6 : η 6 = G := by simp [η]
  have hs (a b : Nat) : graphRel (η 6) a b ↔
      ∃ r, r<n ∧ a=(ordinal r).code ∧ b=(ordinal (l+r)).code := by
    rw [hv6]; exact shift_graphRel l n a b
  have hb : bijectionFormula.Realize η := by
    apply (bijection_meaning η graphRel hg23 hg24 hg43).mpr
    constructor
    · intro a ha
      have ha' : (⟨a⟩ : Object) ∈ ordinal n := by
        change bit (ordinal n).code a = true
        simpa [hv0] using ha
      obtain ⟨r,hr,he⟩ := (mem_ordinal _ _).mp ha'
      have hae : a=(ordinal r).code := congrArg Object.code he
      refine ⟨(ordinal (l+r)).code, ?_, (hs a _).mpr ⟨r,hr,hae,rfl⟩, ?_⟩
      · rw [hv1]
        change ordinal (l+r) ∈ ordinalInterval l (l+n)
        exact (mem_interval _ _ _).mpr ⟨l+r,by omega,by omega,rfl⟩
      · intro b' _ hb'
        obtain ⟨s,_,has,hbs⟩ := (hs a b').mp hb'
        have hrs : r=s := ordinal_code_strictMono.injective (hae.symm.trans has)
        simpa [← hrs] using hbs
    · intro b hb'
      have hbi : bit (ordinalInterval l (l+n)).code b = true := by simpa [hv1] using hb'
      obtain ⟨a,ha,hg⟩ := (interval_shift_edge l n b).mp hbi
      refine ⟨a,by simpa [hv0] using ha,by simpa [hv6] using hg,?_⟩
      intro a' _ ha'
      obtain ⟨r,_,har,hbr⟩ := (hs a b).mp (by simpa [hv6] using hg)
      obtain ⟨s,_,has,hbs⟩ := (hs a' b).mp ha'
      have hrs : l+r=l+s := ordinal_code_strictMono.injective (hbr.symm.trans hbs)
      have : r=s := by omega
      calc
        a' = (ordinal s).code := has
        _ = (ordinal r).code := by rw [this]
        _ = a := har.symm
  have ho : orderFormula.Realize η := by
    apply (order_meaning η graphRel hg23 hg45).mpr
    intro a c b d _ _ _ _ hab hcd
    obtain ⟨r,_,ha,hb⟩ := (hs a b).mp hab
    obtain ⟨s,_,hc,hd⟩ := (hs c d).mp hcd
    subst a; subst b; subst c; subst d
    change (ordinal r ∈ ordinal s) ↔ (ordinal (l+r) ∈ ordinal (l+s))
    simp
  change ∃ g, ¬ (bijectionFormula.Realize (update ρ 6 g) →
    ¬ orderFormula.Realize (update ρ 6 g))
  exact ⟨G, fun h => h hb ho⟩

/-- A two-way unique relation between ordinal `n` and `[l,l+m)` has equal
finite cardinalities. No order or represented-graph premise is required. -/
theorem interval_bijection_cardinality (l n m : Nat) (R : Nat → Nat → Prop)
    (forward : ∀ a, bit (ordinal n).code a = true →
      ∃ b, bit (ordinalInterval l (l+m)).code b = true ∧ R a b ∧
        ∀ b', bit (ordinalInterval l (l+m)).code b' = true → R a b' → b'=b)
    (reverse : ∀ b, bit (ordinalInterval l (l+m)).code b = true →
      ∃ a, bit (ordinal n).code a = true ∧ R a b ∧
        ∀ a', bit (ordinal n).code a' = true → R a' b → a'=a) : n=m := by
  classical
  have shift_mem (r : Nat) (hr : r<m) :
      bit (ordinalInterval l (l+m)).code (ordinal (l+r)).code = true := by
    change ordinal (l+r) ∈ ordinalInterval l (l+m)
    exact (mem_interval _ _ _).mpr ⟨l+r,by omega,by omega,rfl⟩
  have interval_index (b : Nat) (hb : bit (ordinalInterval l (l+m)).code b = true) :
      ∃ r, r<m ∧ b=(ordinal (l+r)).code := by
    have hm : (⟨b⟩ : Object) ∈ ordinalInterval l (l+m) := hb
    obtain ⟨k,hlo,hhi,hk⟩ := (mem_interval _ _ _).mp hm
    refine ⟨k-l,by omega,?_⟩
    have : l+(k-l)=k := by omega
    simpa [this] using congrArg Object.code hk
  have fwd : ∀ i : Fin n, ∃ j : Fin m,
      R (ordinal i.val).code (ordinal (l+j.val)).code := by
    intro i
    obtain ⟨b,hb,hr,_⟩ := forward _ (ordinal_member i.isLt)
    obtain ⟨j,hj,hbj⟩ := interval_index b hb
    exact ⟨⟨j,hj⟩,by simpa [hbj] using hr⟩
  choose f hf using fwd
  have hinj : Function.Injective f := by
    intro i j h
    obtain ⟨a,_,_,uniq⟩ := reverse _ (shift_mem (f i).val (f i).isLt)
    have hi := uniq _ (ordinal_member i.isLt) (hf i)
    have hjR : R (ordinal j.val).code (ordinal (l+(f i).val)).code := by simpa [h] using hf j
    have hj := uniq _ (ordinal_member j.isLt) hjR
    exact Fin.ext (ordinal_code_strictMono.injective (hi.trans hj.symm))
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨a,ha,har,_⟩ := reverse _ (shift_mem j.val j.isLt)
    have ha' : (⟨a⟩ : Object) ∈ ordinal n := ha
    obtain ⟨i,hi,hai⟩ := (mem_ordinal _ _).mp ha'
    have hacode : a=(ordinal i).code := congrArg Object.code hai
    let ii : Fin n := ⟨i,hi⟩
    have hiR : R (ordinal i).code (ordinal (l+j.val)).code := by simpa [hacode] using har
    obtain ⟨b,_,_,uniq⟩ := forward _ (ordinal_member hi)
    have hjEq := uniq _ (shift_mem j.val j.isLt) hiR
    have hfiEq := uniq _ (shift_mem (f ii).val (f ii).isLt) (hf ii)
    have hc : l+(f ii).val=l+j.val := ordinal_code_strictMono.injective (hfiEq.trans hjEq.symm)
    exact ⟨ii,Fin.ext (Nat.add_left_cancel hc)⟩
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  simpa using hc

/-- The concrete candidate equivalence relates a standard ordinal to an
interval precisely when their finite lengths agree. -/
theorem standard_interval_equivalent_iff (ρ : Environment) (l n m : Nat)
    (h0 : ρ 0 = (ordinal n).code)
    (h1 : ρ 1 = (ordinalInterval l (l+m)).code) :
    equivalentFormula.Realize ρ ↔ n=m := by
  constructor
  · intro h
    change ∃ g, ¬ (bijectionFormula.Realize (update ρ 6 g) →
      ¬ orderFormula.Realize (update ρ 6 g)) at h
    obtain ⟨g,hg⟩ := h
    have hb : bijectionFormula.Realize (update ρ 6 g) := Classical.byContradiction (by
      intro hnb; exact hg (fun hb => (hnb hb).elim))
    have h23 : ∀ σ, (graphFormula 6 2 3).Realize σ ↔ graphRel (σ 6) (σ 2) (σ 3) := by
      intro σ; exact graphFormula_realize_iff 6 2 3 σ (by decide) (by decide) (by decide)
    have h24 : ∀ σ, (graphFormula 6 2 4).Realize σ ↔ graphRel (σ 6) (σ 2) (σ 4) := by
      intro σ; exact graphFormula_realize_iff 6 2 4 σ (by decide) (by decide) (by decide)
    have h43 : ∀ σ, (graphFormula 6 4 3).Realize σ ↔ graphRel (σ 6) (σ 4) (σ 3) := by
      intro σ; exact graphFormula_realize_iff 6 4 3 σ (by decide) (by decide) (by decide)
    have ⟨hf,hr⟩ := (bijection_meaning (update ρ 6 g) graphRel h23 h24 h43).mp hb
    apply interval_bijection_cardinality l n m (graphRel g)
    · simpa [update,h0,h1] using hf
    · simpa [update,h0,h1] using hr
  · intro h
    subst m
    exact standard_shift_equivalent ρ l n h0 h1

end PASoundness.PAtoCompactOrdinalShiftGraph

#print axioms PASoundness.PAtoCompactOrdinalShiftGraph.shift_graphRel
#print axioms PASoundness.PAtoCompactOrdinalShiftGraph.interval_shift_edge
#print axioms PASoundness.PAtoCompactOrdinalShiftGraph.standard_shift_equivalent
#print axioms PASoundness.PAtoCompactOrdinalShiftGraph.standard_interval_equivalent_iff
