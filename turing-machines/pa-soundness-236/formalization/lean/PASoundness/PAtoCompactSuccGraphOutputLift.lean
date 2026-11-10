import PASoundness.PAtoCompactSuccTermTotality

/-! Capture-safe existential lifting of pointwise quotient-successor output
transport into successor term-graph output transport. The required relation
transport remains an explicit finite K proof input. -/
namespace PASoundness.PAtoCompactSuccGraphOutputLift

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactSuccTermReplacement
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Lift a guarded pointwise implication through an existential antecedent.
Both displayed vacuity proofs are actual finite K derivations. -/
def guarded_exists_left (x G M T : Nat)
    (vg : KDerivation (imp G (allCode x G)))
    (vt : KDerivation (imp T (allCode x T)))
    (pointwise : KDerivation (imp G (imp M T))) :
    KDerivation (imp G (imp (existsCode x M) T)) := by
  have hall : Context [G] (allCode x (imp M T)) := by
    apply generalizeOne x vg
    exact .mp (Context.head [] G) (.closed pointwise)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.existsElim vt (Context.under hall (existsCode x M))
    (Context.head [G] (existsCode x M))

/-- Pointwise transport of the successor relation, under the output candidate
and output-equivalence conditions, lifts to the complete successor graph.
The source and output names must be below the existential witness name `b`;
`q` and `r` may be equal. -/
noncomputable def succ_output_lift {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q r : Nat) (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ t.varFinset, v a < b)
    (relation : KDerivation (imp (domainAt b r).encode
      (imp (equivAt b q r).encode
        (imp (succAt b b q).encode (succAt b b r).encode)))) :
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph v (.func .succ ![t]) q b).encode
        (imp (equivAt b q r).encode
          (termGraph v (.func .succ ![t]) r b).encode))) := by
  let G := andF (domainAt b r) (equivAt b q r)
  let M := andF (termGraph v t b (b+64)) (succAt b b q)
  let M' := andF (termGraph v t b (b+64)) (succAt b b r)
  let T := termGraph v (.func .succ ![t]) r b
  have hG : b ∉ G.free := by
    intro h
    simp only [G, andF_free, Finset.mem_union] at h
    rcases h with hd | he
    · have hh := domainAt_free b r hd
      simp only [Finset.mem_singleton] at hh
      omega
    · have hh := equivAt_free b q r he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh <;> omega
  have hT : b ∉ T.free := by
    intro h
    have hh := termGraph_free_subset v (.func .succ ![t]) r b h
    simp only [FirstOrder.Language.Term.varFinset, Finset.mem_union, Finset.mem_image,
      Finset.mem_singleton] at hh
    rcases hh with ⟨a, ha, he⟩ | he
    · have ha' : a ∈ t.varFinset := by simpa using ha
      have := hv a ha'
      omega
    · omega
  have hMb : b ∉ M'.binders := by
    simp only [M', andF_binders, Finset.mem_union, not_or]
    exact ⟨termGraph_below_not_binder v t b (b+64) b (by omega),
      succAt_below_not_binder b b r b (by omega)⟩
  have hi := CompactNamed.existsIntroduce b M' hMb
  have hpoint : KDerivation (imp G.encode (imp M.encode T.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode, G.encode]
    have hg : Context Γ (both (domainAt b r).encode (equivAt b q r).encode) := by
      have h := Context.head [] G.encode
      have h := Context.under h M.encode
      simpa [Γ, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
    have hm : Context Γ (both (termGraph v t b (b+64)).encode (succAt b b q).encode) := by
      have h := Context.head [G.encode] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
    have hd := Context.conjunctionLeft hg
    have he := Context.conjunctionRight hg
    have hc := Context.conjunctionLeft hm
    have hs := Context.conjunctionRight hm
    have hs' : Context Γ (succAt b b r).encode := .mp hs (.mp he (.mp hd (.closed relation)))
    have hboth := Context.conjunctionIntro hc hs'
    have hm' : Context Γ M'.encode := by
      simpa [M', andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hboth
    have hex : Context Γ (existsCode b M'.encode) := .mp hm' (.closed hi)
    have ht := Context.conjunctionIntro hd hex
    simpa [T, M', termGraph, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg, existsCode] using ht
  have hlift := guarded_exists_left b G.encode M.encode T.encode (free_vacuity b G hG)
    (free_vacuity b T hT) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt b q r).encode, (termGraph v (.func .succ ![t]) q b).encode,
    (domainAt b r).encode]
  have he : Context Γ (equivAt b q r).encode := Context.head _ _
  have hs : Context Γ (termGraph v (.func .succ ![t]) q b).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt b r).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ G.encode := by
    have hh := Context.conjunctionIntro hd he
    simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
  have hs' : Context Γ (existsCode b M.encode) := by
    have hh : Context Γ (both (domainAt b q).encode (existsCode b M.encode)) := by
      simpa [termGraph, M, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode,
        both, neg, existsCode] using hs
    exact Context.conjunctionRight hh
  exact .mp hs' (.mp hg (.closed hlift))

end PASoundness.PAtoCompactSuccGraphOutputLift

#print axioms PASoundness.PAtoCompactSuccGraphOutputLift.guarded_exists_left
#print axioms PASoundness.PAtoCompactSuccGraphOutputLift.succ_output_lift
