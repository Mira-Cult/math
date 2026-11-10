import PASoundness.PAtoCompactSuccBaseMultiAlpha
import PASoundness.PAtoCompactTermGraphReplace
import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PAtoCompactZeroTermBaseTransport
import PASoundness.PAtoCompactSuccTermReplacement

/-! Conditional finite K transport for the successor term node. The recursive
child graph must be transported at its existing output witness first; its
forward and reverse derivations are explicit inputs, not semantic shortcuts. -/
namespace PASoundness.PAtoCompactSuccTermTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactTermGraphReplace
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactSuccTermReplacement
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactZeroTermBaseTransport

/-- A successor body whose child output retains `old` while its private
blocks have moved to `base`. -/
def rebasedBody {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (old base out : Nat) : Formula :=
  andF (termGraph v t old (base + 64)) (succAt base old out)

theorem old_not_rebased_binder {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (old base out : Nat) (ho : old < base) : old ∉ (rebasedBody v t old base out).binders := by
  intro h
  simp only [rebasedBody, andF_binders, Finset.mem_union] at h
  rcases h with hc | hs
  · have hh := termGraph_binder_range v t old (base + 64) old hc
    omega
  · have hh := succAt_private base old out old hs
    omega

theorem base_not_rebased_names {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (old base out : Nat)
    (ho : old < base) (hout : out < base)
    (hv : ∀ a ∈ t.varFinset, v a < base) : base ∉ (rebasedBody v t old base out).names := by
  intro h
  simp only [rebasedBody, andF, CompactNamed.Formula.not, Formula.names,
    Finset.union_empty, Finset.mem_union] at h
  rcases h with hc | hs
  · rw [Formula.names_eq_free_union_binders] at hc
    rcases Finset.mem_union.mp hc with hf | hb
    · have hh := termGraph_free_subset v t old (base + 64) hf
      rcases Finset.mem_union.mp hh with hm | hm
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
        have := hv a ha
        omega
      · have := Finset.mem_singleton.mp hm
        omega
    · have hh := termGraph_binder_range v t old (base + 64) base hb
      omega
  · rcases succAt_name_bound base old out base hs with hs | hs | hs <;> omega

theorem replace_rebasedBody {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (old base out : Nat)
    (ho : old < base) (hout : out < old)
    (hv : ∀ a ∈ t.varFinset, v a < old) :
    replace old base (rebasedBody v t old base out) = rebasedBody v t base base out := by
  unfold rebasedBody andF
  simp only [CompactNamed.Formula.not, replace]
  rw [replace_termGraph v t old (base + 64) old base (by omega)]
  rw [replace_succAt base old out old base (by omega)]
  have hmap : ∀ a ∈ t.varFinset, (rename old base ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old by have := hv a ha; omega]
  rw [termGraph_name_agree t (rename old base ∘ v) v hmap]
  simp [rename, show out ≠ old by omega]

/-- Once the child graph has been rebased, move its existential witness from
`old` to the fresh intermediate base. Input/output labels stay unchanged. -/
def rebased_exists_alpha {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (old base out : Nat)
    (ho : old < base) (hout : out < old)
    (hv : ∀ a ∈ t.varFinset, v a < old) :
    ProofEquiv (.ex old (rebasedBody v t old base out))
      (.ex base (rebasedBody v t base base out)) := by
  have h := ProofEquiv.alphaExists old base (rebasedBody v t old base out)
    (by omega) (old_not_rebased_binder v t old base out ho)
    (base_not_rebased_names v t old base out ho (by omega)
      (by intro a ha; have := hv a ha; omega))
  rw [replace_rebasedBody v t old base out ho hout hv] at h
  exact h

/-- A successor node moves to a higher base when both directions of the
recursive child-base transport at the old output witness are supplied. -/
def succTerm_ordered {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (old base out : Nat)
    (ho : old < base) (hout : out < old)
    (hv : ∀ a ∈ t.varFinset, v a < old)
    (childF : KDerivation (imp (termGraph v t old (old + 64)).encode
      (termGraph v t old (base + 64)).encode))
    (childB : KDerivation (imp (termGraph v t old (base + 64)).encode
      (termGraph v t old (old + 64)).encode)) :
    KDerivation (imp (termGraph v (.func .succ ![t]) out old).encode
      (termGraph v (.func .succ ![t]) out base).encode) ×
    KDerivation (imp (termGraph v (.func .succ ![t]) out base).encode
      (termGraph v (.func .succ ![t]) out old).encode) := by
  have hsucc := succAt_base_alpha old base old out (by omega) (by omega) (by omega) (by omega)
  have hiF : KDerivation (imp
      (andF (termGraph v t old (old + 64)) (succAt old old out)).encode
      (rebasedBody v t old base out).encode) :=
    andF_transport _ _ _ _ childF hsucc.forward
  have hiB : KDerivation (imp
      (rebasedBody v t old base out).encode
      (andF (termGraph v t old (old + 64)) (succAt old old out)).encode) :=
    andF_transport _ _ _ _ childB hsucc.backward
  have ha := rebased_exists_alpha v t old base out ho hout hv
  have heF := compose (existsCongr old hiF) ha.forward
  have heB := compose ha.backward (existsCongr old hiB)
  have hdF := domainAt_transport old base out (by omega) (by omega)
  have hdB := domainAt_transport base old out (by omega) (by omega)
  constructor
  · change KDerivation (imp (andF (domainAt old out) (.ex old
        (andF (termGraph v t old (old + 64)) (succAt old old out)))).encode
      (andF (domainAt base out) (.ex base (rebasedBody v t base base out))).encode)
    exact andF_transport _ _ _ _ hdF heF
  · change KDerivation (imp (andF (domainAt base out) (.ex base (rebasedBody v t base base out))).encode
      (andF (domainAt old out) (.ex old
        (andF (termGraph v t old (old + 64)) (succAt old old out)))).encode)
    exact andF_transport _ _ _ _ hdB heB

/-- A fixed third parent block exceeds both original parent bases. -/
def intermediateBase (b c : Nat) : Nat := max b c + 1

/-- Arbitrary-base successor-node transport, conditional on four actual K
child derivations at the two original witnesses and a common high child base. -/
def succTerm_base_transport {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b c out : Nat)
    (hbo : out < b) (hco : out < c)
    (hbv : ∀ a ∈ t.varFinset, v a < b) (hcv : ∀ a ∈ t.varFinset, v a < c)
    (hbF : KDerivation (imp (termGraph v t b (b + 64)).encode
      (termGraph v t b (intermediateBase b c + 64)).encode))
    (hbB : KDerivation (imp (termGraph v t b (intermediateBase b c + 64)).encode
      (termGraph v t b (b + 64)).encode))
    (hcF : KDerivation (imp (termGraph v t c (c + 64)).encode
      (termGraph v t c (intermediateBase b c + 64)).encode))
    (hcB : KDerivation (imp (termGraph v t c (intermediateBase b c + 64)).encode
      (termGraph v t c (c + 64)).encode)) :
    KDerivation (imp (termGraph v (.func .succ ![t]) out b).encode
      (termGraph v (.func .succ ![t]) out c).encode) ×
    KDerivation (imp (termGraph v (.func .succ ![t]) out c).encode
      (termGraph v (.func .succ ![t]) out b).encode) := by
  have hbd : b < intermediateBase b c := by unfold intermediateBase; omega
  have hcd : c < intermediateBase b c := by unfold intermediateBase; omega
  have hb := succTerm_ordered v t b (intermediateBase b c) out hbd hbo hbv hbF hbB
  have hc := succTerm_ordered v t c (intermediateBase b c) out hcd hco hcv hcF hcB
  exact ⟨compose hb.1 hc.2, compose hc.1 hb.2⟩

theorem succTerm_base_forward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b c out : Nat)
    (hbo : out < b) (hco : out < c)
    (hbv : ∀ a ∈ t.varFinset, v a < b) (hcv : ∀ a ∈ t.varFinset, v a < c)
    (hbF : KDerivation (imp (termGraph v t b (b + 64)).encode
      (termGraph v t b (intermediateBase b c + 64)).encode))
    (hbB : KDerivation (imp (termGraph v t b (intermediateBase b c + 64)).encode
      (termGraph v t b (b + 64)).encode))
    (hcF : KDerivation (imp (termGraph v t c (c + 64)).encode
      (termGraph v t c (intermediateBase b c + 64)).encode))
    (hcB : KDerivation (imp (termGraph v t c (intermediateBase b c + 64)).encode
      (termGraph v t c (c + 64)).encode)) :
    theoremCode (certificate (succTerm_base_transport v t b c out hbo hco hbv hcv hbF hbB hcF hcB).1) =
      imp (termGraph v (.func .succ ![t]) out b).encode
        (termGraph v (.func .succ ![t]) out c).encode := certificate_correct _

theorem succTerm_base_backward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b c out : Nat)
    (hbo : out < b) (hco : out < c)
    (hbv : ∀ a ∈ t.varFinset, v a < b) (hcv : ∀ a ∈ t.varFinset, v a < c)
    (hbF : KDerivation (imp (termGraph v t b (b + 64)).encode
      (termGraph v t b (intermediateBase b c + 64)).encode))
    (hbB : KDerivation (imp (termGraph v t b (intermediateBase b c + 64)).encode
      (termGraph v t b (b + 64)).encode))
    (hcF : KDerivation (imp (termGraph v t c (c + 64)).encode
      (termGraph v t c (intermediateBase b c + 64)).encode))
    (hcB : KDerivation (imp (termGraph v t c (intermediateBase b c + 64)).encode
      (termGraph v t c (c + 64)).encode)) :
    theoremCode (certificate (succTerm_base_transport v t b c out hbo hco hbv hcv hbF hbB hcF hcB).2) =
      imp (termGraph v (.func .succ ![t]) out c).encode
        (termGraph v (.func .succ ![t]) out b).encode := certificate_correct _

end PASoundness.PAtoCompactSuccTermTransport

#print axioms PASoundness.PAtoCompactSuccTermTransport.old_not_rebased_binder
#print axioms PASoundness.PAtoCompactSuccTermTransport.base_not_rebased_names
#print axioms PASoundness.PAtoCompactSuccTermTransport.replace_rebasedBody
#print axioms PASoundness.PAtoCompactSuccTermTransport.rebased_exists_alpha
#print axioms PASoundness.PAtoCompactSuccTermTransport.succTerm_ordered
#print axioms PASoundness.PAtoCompactSuccTermTransport.succTerm_base_transport
#print axioms PASoundness.PAtoCompactSuccTermTransport.succTerm_base_forward_certificate
#print axioms PASoundness.PAtoCompactSuccTermTransport.succTerm_base_backward_certificate
