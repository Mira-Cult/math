import PASoundness.PAtoCompactTermSubstZeroLeaf
import PASoundness.PAtoCompactTermSubstInduction
import PASoundness.PAtoCompactAllTermTransport

/-! Retained-zero graph alignment at one variable occurrence. Forward zero
output transport is an explicit finite K proof input in this draft. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRetainedZeroLeaf
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstInduction
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactTermSubstZeroLeaf
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rebase the retained graph of zero, then align a variable graph and zero
graph at an arbitrary output. The argument `ho` is the still-explicit finite K
zero-output transport. Guard and graph witnesses are kept object-level. -/
noncomputable def retained_zero_leaf (g : Formula) (q d b out : Nat)
    (hqd : q < d) (hq : q < b) (hout : out < b)
    (ho : KDerivation (imp (domainAt b out).encode
      (imp (termGraph id Peano.zero q b).encode
        (imp (equivAt b q out).encode (termGraph id Peano.zero out b).encode)))) :
    Align (andF g (termGraph id Peano.zero q d)) (.var q) Peano.zero b out := by
  let H := andF g (termGraph id Peano.zero q d)
  let G := (termGraph id Peano.zero q d).encode
  let Gb := (termGraph id Peano.zero q b).encode
  let V := (termGraph id (.var q : Peano.Term) out b).encode
  let T := (termGraph id Peano.zero out b).encode
  have hvd : ∀ a ∈ Peano.zero.varFinset, id a < d := by
    intro a ha; simp [Peano.zero, Term.varFinset] at ha
  have hvb : ∀ a ∈ Peano.zero.varFinset, id a < b := by
    intro a ha; simp [Peano.zero, Term.varFinset] at ha
  have hmove := (termGraph_base_transport id Peano.zero d b q hqd hq hvd hvb).1
  have hf := zero_leaf_forward b q out ho
  have hr := zero_leaf_reverse b q out (by omega) (by omega)
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [V,H.encode]
    have hH : Context Γ (both g.encode G) := by
      have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
      simpa [H, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    have hV : Context Γ V := Context.head _ _
    have hGb : Context Γ Gb := .mp (Context.conjunctionRight hH) (.closed hmove)
    exact .mp hV (.mp hGb (.closed hf))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [T,H.encode]
    have hH : Context Γ (both g.encode G) := by
      have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
      simpa [H, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    have hT : Context Γ T := Context.head _ _
    have hGb : Context Γ Gb := .mp (Context.conjunctionRight hH) (.closed hmove)
    exact .mp hT (.mp hGb (.closed hr))

end PASoundness.PAtoCompactRetainedZeroLeaf

#print axioms PASoundness.PAtoCompactRetainedZeroLeaf.retained_zero_leaf
