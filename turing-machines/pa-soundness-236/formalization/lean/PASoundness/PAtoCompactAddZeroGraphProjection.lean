import PASoundness.PAtoCompactAddZeroGraphOutput

/-! Extract the original child witness from a right-zero addition graph. -/
namespace PASoundness.PAtoCompactAddZeroGraphProjection
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactZeroBaseTransport

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Finite K extraction of the original child graph and its quotient
connection to the output, with both source/output names below the allocator. -/
noncomputable def project_child {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b p : Nat) (hp : p < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
      (existsCode b (andF (termGraph v t b (b+64)) (equivAt b b p)).encode)) := by
  let L := termGraph v t b (b+64)
  let Z := termGraph v (.func .zero Fin.elim0) (b+1) (b+64+termCost t)
  let M := andF L (andF Z (addAt b b (b+1) p))
  let N := andF L (equivAt b b p)
  have hN : b+1 ∉ N.free := by
    intro h
    simp only [N, andF_free, Finset.mem_union] at h
    rcases h with hL | hE
    · have hh := termGraph_free_subset v t b (b+64) hL
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
        have hlt := hv a ha
        omega
      · have he := Finset.mem_singleton.mp hh
        omega
    · have hh := equivAt_free b b p hE
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with he | he <;> omega
  have hf := PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated.schema_of_fixed
    false b b (b+1) p (by omega) (by omega) (by omega)
    PASoundness.PAtoCompactAdditionRightZeroSchemaFixed.fixed_forward
  change KDerivation (imp (zeroAt b (b+1)).encode
    (imp (addAt b b (b+1) p).encode (equivAt b b p).encode)) at hf
  have point : KDerivation (imp M.encode N.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [M.encode]
    have hM : Context Γ (both L.encode (both Z.encode (addAt b b (b+1) p).encode)) := by
      have hh := Context.head [] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hh
    have hL := Context.conjunctionLeft hM
    have hZ := Context.conjunctionLeft (Context.conjunctionRight hM)
    have hAdd := Context.conjunctionRight (Context.conjunctionRight hM)
    have hzChild : Context Γ (zeroAt (b+64+termCost t) (b+1)).encode := by
      have hz : Context Γ (both (domainAt (b+64+termCost t) (b+1)).encode
          (zeroAt (b+64+termCost t) (b+1)).encode) := by
        simpa [Z, termGraph, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hZ
      exact Context.conjunctionRight hz
    have hz := Context.mp hzChild (.closed (zeroAt_base_forward (b+64+termCost t) b (b+1) (by omega) (by omega)))
    have he := Context.mp hAdd (Context.mp hz (.closed hf))
    have hn := Context.conjunctionIntro hL he
    simpa [N, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hn
  have inner : KDerivation (imp (existsCode (b+1) M.encode) N.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (free_vacuity (b+1) N hN) (.closed (.generalize (b+1) point))
      (Context.head [] _)
  have outer := existsCongr b inner
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode]
  have hA : Context Γ (both (domainAt b p).encode (existsCode b (existsCode (b+1) M.encode))) := by
    have hh : Context Γ (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode :=
      Context.head [] _
    simpa [Γ, binaryTerm, binaryRel, termGraph, M, L, Z, andF,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hh
  exact .mp (Context.conjunctionRight hA) (.closed outer)

theorem project_child_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b p : Nat) (hp : p < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    theoremCode (certificate (project_child v t b p hp hv)) =
      imp (termGraph v (binaryTerm true t (.func .zero Fin.elim0)) p b).encode
        (existsCode b (andF (termGraph v t b (b+64)) (equivAt b b p)).encode) :=
  certificate_correct _
end PASoundness.PAtoCompactAddZeroGraphProjection

#print axioms PASoundness.PAtoCompactAddZeroGraphProjection.project_child
#print axioms PASoundness.PAtoCompactAddZeroGraphProjection.project_child_certificate
