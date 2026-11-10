import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactTermZeroGuarded
import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactDynamicTransitivityFinal
import PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated
import PASoundness.PAtoCompactAdditionRightZeroSchemaFixed

/-! Finite K output transport for the actual generated graph of `t + 0`.
The proof retains and reuses both original child witnesses. It constructs no
term graph existence or functionality proof. -/
namespace PASoundness.PAtoCompactAddZeroGraphOutput

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactDynamicTransitivityFinal

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Reuse both child witnesses, given the exact two directed right-zero
schemas. Names lie below the first existential witness; aliases are allowed. -/
noncomputable def add_zero_output_lift {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm true t (.func .zero Fin.elim0)).varFinset, v a < b)
    (forward : KDerivation (imp (zeroAt b (b+1)).encode
      (imp (addAt b b (b+1) q).encode (equivAt b b q).encode)))
    (backward : KDerivation (imp (zeroAt b (b+1)).encode
      (imp (equivAt b b r).encode (addAt b b (b+1) r).encode))) :
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode
        (imp (equivAt b q r).encode
          (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) r b).encode))) := by
  let G := andF (domainAt b r) (equivAt b q r)
  let L := termGraph v t b (b+64)
  let R := termGraph v (.func .zero Fin.elim0) (b+1) (b+64+termCost t)
  let M := andF L (andF R (binaryRel true b b (b+1) q))
  let T := termGraph v (binaryTerm true t (.func .zero Fin.elim0)) r b
  have hG (k : Nat) (hk : b ≤ k) : k ∉ G.free := by
    intro h
    simp only [G, andF_free, Finset.mem_union] at h
    rcases h with hd | he
    · have hh := domainAt_free b r hd
      simp only [Finset.mem_singleton] at hh
      omega
    · have hh := equivAt_free b q r he
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with hh | hh <;> omega
  have hT (k : Nat) (hk : b ≤ k) : k ∉ T.free := by
    intro h
    have hh := termGraph_free_subset v (binaryTerm true t (.func .zero Fin.elim0)) r b h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
    rcases hh with ⟨a, ha, he⟩ | he
    · have ha' := hv a ha
      omega
    · omega
  have introGraph := binary_from_witness v true t (.func .zero Fin.elim0) b r
  have hpoint : KDerivation (imp G.encode (imp M.encode T.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode, G.encode]
    have hg : Context Γ (both (domainAt b r).encode (equivAt b q r).encode) := by
      have h := Context.head [] G.encode
      have h := Context.under h M.encode
      simpa [Γ, G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
    have hm : Context Γ (both L.encode (both R.encode (binaryRel true b b (b+1) q).encode)) := by
      have h := Context.head [G.encode] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
    have hd := Context.conjunctionLeft hg
    have he := Context.conjunctionRight hg
    have hl := Context.conjunctionLeft hm
    have hr' := Context.conjunctionLeft (Context.conjunctionRight hm)
    have hrel := Context.conjunctionRight (Context.conjunctionRight hm)
    have hDchild := Context.mp hl (.closed (termGraph_domain v t b (b+64)))
    have hD : Context Γ (domainAt b b).encode := Context.mp hDchild
      (.closed (domainAt_transport (b+64) b b (by omega) (by omega)))
    have hzerochild : Context Γ (zeroAt (b+64+termCost t) (b+1)).encode := by
      have hh : Context Γ (both (domainAt (b+64+termCost t) (b+1)).encode
          (zeroAt (b+64+termCost t) (b+1)).encode) := by
        simpa [R, termGraph, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using hr'
      exact Context.conjunctionRight hh
    have hzero : Context Γ (zeroAt b (b+1)).encode := Context.mp hzerochild
      (.closed (zeroAt_base_forward _ _ _ (by omega) (by omega)))
    have hrelq : Context Γ (addAt b b (b+1) q).encode := by simpa [binaryRel] using hrel
    have heq := Context.mp hrelq (Context.mp hzero (.closed forward))
    have htrans := dynamic_transitivity b b q r (by omega) (by omega) (by omega)
    have heqr := Context.mp he (Context.mp heq (Context.mp hD (.closed htrans)))
    have hrel' : Context Γ (binaryRel true b b (b+1) r).encode := by
      simpa [binaryRel] using Context.mp heqr (Context.mp hzero (.closed backward))
    exact .mp hrel' (.mp hr' (.mp hl (.mp hd (.closed introGraph))))
  have inner := guarded_exists_left (b+1) G.encode M.encode T.encode
    (free_vacuity (b+1) G (hG (b+1) (by omega)))
    (free_vacuity (b+1) T (hT (b+1) (by omega))) hpoint
  have outer := guarded_exists_left b G.encode (existsCode (b+1) M.encode) T.encode
    (free_vacuity b G (hG b (by omega)))
    (free_vacuity b T (hT b (by omega))) inner
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt b q r).encode, (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode,
    (domainAt b r).encode]
  have he : Context Γ (equivAt b q r).encode := Context.head _ _
  have hs : Context Γ (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt b r).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ G.encode := by
    have h := Context.conjunctionIntro hd he
    simpa [G, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
  have hex : Context Γ (existsCode b (existsCode (b+1) M.encode)) := by
    have h : Context Γ (both (domainAt b q).encode
        (existsCode b (existsCode (b+1) M.encode))) := by
      simpa [binaryTerm, binaryRel, termGraph, M, L, R, andF,
        CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hs
    exact Context.conjunctionRight h
  exact .mp hex (.mp hg (.closed outer))

theorem add_zero_output_lift_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm true t (.func .zero Fin.elim0)).varFinset, v a < b)
    (forward : KDerivation (imp (zeroAt b (b+1)).encode
      (imp (addAt b b (b+1) q).encode (equivAt b b q).encode)))
    (backward : KDerivation (imp (zeroAt b (b+1)).encode
      (imp (equivAt b b r).encode (addAt b b (b+1) r).encode))) :
    theoremCode (certificate (add_zero_output_lift v t b q r hq hr hv forward backward)) =
      imp (domainAt b r).encode (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode
        (imp (equivAt b q r).encode (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) r b).encode)) :=
  certificate_correct _

/-- Actual output transport for the graph of `t + 0`, with no K-proof
premises. The input term is arbitrary; no totality or functionality is used. -/
noncomputable def add_zero_output {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm true t (.func .zero Fin.elim0)).varFinset, v a < b) :
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode
        (imp (equivAt b q r).encode
          (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) r b).encode))) := by
  have hf := PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated.schema_of_fixed
    false b b (b+1) q (by omega) (by omega) (by omega)
    PASoundness.PAtoCompactAdditionRightZeroSchemaFixed.fixed_forward
  have hb := PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated.schema_of_fixed
    true b b (b+1) r (by omega) (by omega) (by omega)
    PASoundness.PAtoCompactAdditionRightZeroSchemaFixed.fixed_backward
  change KDerivation (imp (zeroAt b (b+1)).encode
    (imp (addAt b b (b+1) q).encode (equivAt b b q).encode)) at hf
  change KDerivation (imp (zeroAt b (b+1)).encode
    (imp (equivAt b b r).encode (addAt b b (b+1) r).encode)) at hb
  exact add_zero_output_lift v t b q r hq hr hv hf hb

theorem add_zero_output_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ (binaryTerm true t (.func .zero Fin.elim0)).varFinset, v a < b) :
    theoremCode (certificate (add_zero_output v t b q r hq hr hv)) =
      imp (domainAt b r).encode
        (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) q b).encode
          (imp (equivAt b q r).encode
            (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) r b).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactAddZeroGraphOutput

#print axioms PASoundness.PAtoCompactAddZeroGraphOutput.add_zero_output_lift
#print axioms PASoundness.PAtoCompactAddZeroGraphOutput.add_zero_output_lift_certificate
#print axioms PASoundness.PAtoCompactAddZeroGraphOutput.add_zero_output
#print axioms PASoundness.PAtoCompactAddZeroGraphOutput.add_zero_output_certificate
