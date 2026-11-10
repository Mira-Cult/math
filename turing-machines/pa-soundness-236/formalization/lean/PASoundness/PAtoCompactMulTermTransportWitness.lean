import PASoundness.CompactFreshen
import PASoundness.PAtoCompactTermGraphReplace
import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactGuardElimination

/-! Two capture-safe existential witness moves as finite K proof data. This
is a generic ingredient and does not rebase arithmetic term graphs. -/
namespace PASoundness.PAtoCompactMulTermTransportWitness

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphReplace
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactGuardElimination

/-- Move both enclosing witnesses to fresh labels. The order of the literal
replacements is significant. Bounds here concern syntactic names, not the
values assigned to those names. -/
def two_exists_alpha (f : Formula) (x y u v : Nat)
    (hxu : x ≠ u) (hxy : x ≠ y) (hyu : y ≠ u)
    (hyv : y ≠ v) (huv : u ≠ v)
    (hxb : x ∉ f.binders) (hyb : y ∉ f.binders)
    (huf : u ∉ f.names) (hvf : v ∉ f.names) :
    ProofEquiv (.ex x (.ex y f))
      (.ex u (.ex v (replace y v (replace x u f)))) := by
  have h1 := ProofEquiv.alphaExists x u (.ex y f) hxu
    (by simpa [Formula.binders, hxy] using hxb)
    (by simpa [Formula.names, Ne.symm hyu] using huf)
  have hvnew : v ∉ (replace x u f).names := by
    intro hv
    have hv' := replace_names_subset x u f hv
    rcases Finset.mem_insert.mp hv' with he | hf
    · exact huv he.symm
    · exact hvf hf
  have h2 := ProofEquiv.alphaExists y v (replace x u f) hyv
    (by simpa [replace_binders] using hyb) hvnew
  exact h1.trans (ProofEquiv.existential u h2)

theorem two_exists_alpha_forward_certificate (f : Formula) (x y u v : Nat)
    (hxu : x ≠ u) (hxy : x ≠ y) (hyu : y ≠ u)
    (hyv : y ≠ v) (huv : u ≠ v)
    (hxb : x ∉ f.binders) (hyb : y ∉ f.binders)
    (huf : u ∉ f.names) (hvf : v ∉ f.names) :
    theoremCode (certificate (two_exists_alpha f x y u v hxu hxy hyu hyv huv hxb hyb huf hvf).forward) =
      imp (Formula.ex x (.ex y f)).encode
        (Formula.ex u (.ex v (replace y v (replace x u f)))).encode := certificate_correct _

theorem two_exists_alpha_backward_certificate (f : Formula) (x y u v : Nat)
    (hxu : x ≠ u) (hxy : x ≠ y) (hyu : y ≠ u)
    (hyv : y ≠ v) (huv : u ≠ v)
    (hxb : x ∉ f.binders) (hyb : y ∉ f.binders)
    (huf : u ∉ f.names) (hvf : v ∉ f.names) :
    theoremCode (certificate (two_exists_alpha f x y u v hxu hxy hyu hyv huv hxb hyb huf hvf).backward) =
      imp (Formula.ex u (.ex v (replace y v (replace x u f)))).encode
        (Formula.ex x (.ex y f)).encode := certificate_correct _

theorem mulAt_below_not_binder (base a b out x : Nat) (hx : x < base + 2) :
    x ∉ (mulAt base a b out).binders := by
  intro h
  have hl := mulAt_private base a b out x h
  omega

/-- Literal replacement commutes with the multiplication template when the
source label is below the private block. Target capture is a separate check. -/
theorem replace_mulAt (base a b out x y : Nat) (hx : x < base + 2) :
    replace x y (mulAt base a b out) =
      mulAt base (rename x y a) (rename x y b) (rename x y out) := by
  rw [← map_eq_replace x y (mulAt base a b out) (mulAt_below_not_binder base a b out x hx)]
  unfold mulAt
  rw [mapNames_compose]
  congr 1
  funext k
  by_cases h0 : k = 0
  · simp [threeMap, h0]
  · by_cases h1 : k = 1
    · simp [threeMap, h1]
    · by_cases h2 : k = 2
      · simp [threeMap, h2]
      · have hne : base + 2 + k ≠ x := by omega
        simp [threeMap, h0, h1, h2, rename, hne]

/-- The binary graph body with old output witnesses and rebased private
blocks. The witnesses may represent identical objects. -/
def rebasedBody {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (old base out : Nat) : Formula :=
  andF (termGraph v t old (base + 64))
    (andF (termGraph v u (old + 1) (base + 64 + termCost t))
      (mulAt base old (old + 1) out))

theorem old_not_rebased_binder {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (old base out w : Nat)
    (ho : old + 1 < base) (hw : w = old ∨ w = old + 1) :
    w ∉ (rebasedBody v t u old base out).binders := by
  intro h
  simp only [rebasedBody, andF_binders, Finset.mem_union] at h
  rcases h with hl | hr | hm
  · have hh := termGraph_binder_range v t old (base + 64) w hl
    omega
  · have hh := termGraph_binder_range v u (old + 1) (base + 64 + termCost t) w hr
    omega
  · have hh := mulAt_private base old (old + 1) out w hm
    omega

theorem new_not_rebased_names {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (old base out w : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (ht : ∀ a ∈ t.varFinset, v a < old) (hu : ∀ a ∈ u.varFinset, v a < old)
    (hw : w = base ∨ w = base + 1) : w ∉ (rebasedBody v t u old base out).names := by
  intro h
  simp only [rebasedBody, andF, CompactNamed.Formula.not, Formula.names,
    Finset.union_empty, Finset.mem_union] at h
  rcases h with hl | hr | hm
  · rw [Formula.names_eq_free_union_binders] at hl
    rcases Finset.mem_union.mp hl with hf | hb
    · have hh := termGraph_free_subset v t old (base + 64) hf
      rcases Finset.mem_union.mp hh with hm | hm
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
        have := ht a ha
        omega
      · have := Finset.mem_singleton.mp hm
        omega
    · have hh := termGraph_binder_range v t old (base + 64) w hb
      omega
  · rw [Formula.names_eq_free_union_binders] at hr
    rcases Finset.mem_union.mp hr with hf | hb
    · have hh := termGraph_free_subset v u (old + 1) (base + 64 + termCost t) hf
      rcases Finset.mem_union.mp hh with hm | hm
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
        have := hu a ha
        omega
      · have := Finset.mem_singleton.mp hm
        omega
    · have hh := termGraph_binder_range v u (old + 1) (base + 64 + termCost t) w hb
      omega
  · rw [Formula.names_eq_free_union_binders] at hm
    rcases Finset.mem_union.mp hm with hf | hb
    · have hh := mulAt_free base old (old + 1) out hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with h | h | h <;> omega
    · have hh := mulAt_private base old (old + 1) out w hb
      omega

/-- Sequentially moving the two old witnesses changes the literal rebased
body to the same body at the new witnesses, without changing its other free
inputs. -/
theorem replace_rebasedBody {α : Type} [DecidableEq α]
    (v : α → Nat) (t u : Peano.language.Term α) (old base out : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (ht : ∀ a ∈ t.varFinset, v a < old) (hu : ∀ a ∈ u.varFinset, v a < old) :
    replace (old + 1) (base + 1) (replace old base (rebasedBody v t u old base out)) =
      rebasedBody v t u base base out := by
  unfold rebasedBody andF
  simp only [CompactNamed.Formula.not, replace]
  rw [replace_termGraph v t old (base + 64) old base (by omega)]
  rw [replace_termGraph v u (old + 1) (base + 64 + termCost t) old base (by omega)]
  rw [replace_mulAt base old (old + 1) out old base (by omega)]
  have hmt : ∀ a ∈ t.varFinset, (rename old base ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old by have := ht a ha; omega]
  have hmu : ∀ a ∈ u.varFinset, (rename old base ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old by have := hu a ha; omega]
  rw [termGraph_name_agree t (rename old base ∘ v) v hmt]
  rw [termGraph_name_agree u (rename old base ∘ v) v hmu]
  simp only [rename, if_true, show old + 1 ≠ old by omega, show out ≠ old by omega,
    if_false]
  rw [replace_termGraph v t base (base + 64) (old + 1) (base + 1) (by omega)]
  rw [replace_termGraph v u (old + 1) (base + 64 + termCost t) (old + 1) (base + 1) (by omega)]
  rw [replace_mulAt base base (old + 1) out (old + 1) (base + 1) (by omega)]
  have hmt' : ∀ a ∈ t.varFinset, (rename (old + 1) (base + 1) ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old + 1 by have := ht a ha; omega]
  have hmu' : ∀ a ∈ u.varFinset, (rename (old + 1) (base + 1) ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old + 1 by have := hu a ha; omega]
  rw [termGraph_name_agree t (rename (old + 1) (base + 1) ∘ v) v hmt']
  rw [termGraph_name_agree u (rename (old + 1) (base + 1) ∘ v) v hmu']
  simp [rename, show base ≠ old + 1 by omega, show out ≠ old + 1 by omega]

/-- Both parent witnesses can be alpha-moved to the fresh rebased block. -/
def rebased_exists_alpha {α : Type} [DecidableEq α]
    (v : α → Nat) (t u : Peano.language.Term α) (old base out : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (ht : ∀ a ∈ t.varFinset, v a < old) (hu : ∀ a ∈ u.varFinset, v a < old) :
    ProofEquiv (.ex old (.ex (old + 1) (rebasedBody v t u old base out)))
      (.ex base (.ex (base + 1) (rebasedBody v t u base base out))) := by
  have h := two_exists_alpha (rebasedBody v t u old base out) old (old + 1) base (base + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (old_not_rebased_binder v t u old base out old ho (Or.inl rfl))
    (old_not_rebased_binder v t u old base out (old + 1) ho (Or.inr rfl))
    (new_not_rebased_names v t u old base out base ho hout ht hu (Or.inl rfl))
    (new_not_rebased_names v t u old base out (base + 1) ho hout ht hu (Or.inr rfl))
  rw [replace_rebasedBody v t u old base out ho hout ht hu] at h
  exact h

end PASoundness.PAtoCompactMulTermTransportWitness

#print axioms PASoundness.PAtoCompactMulTermTransportWitness.two_exists_alpha
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.two_exists_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.two_exists_alpha_backward_certificate
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.mulAt_below_not_binder
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.replace_mulAt
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.old_not_rebased_binder
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.new_not_rebased_names
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.replace_rebasedBody
#print axioms PASoundness.PAtoCompactMulTermTransportWitness.rebased_exists_alpha
