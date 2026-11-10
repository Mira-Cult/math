import PASoundness.PAtoCompactGuardedAllCongruence
import PASoundness.PAtoCompactScopedActiveAll

/-! Capture-safe universal alpha alignment under a retained hypothesis.
The required child alignment is finite K proof data under that same hypothesis.
No soundness theorem is used. -/
namespace PASoundness.PAtoCompactGuardedUniversalAlignment

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedActiveAll
open PASoundness.PAtoCompactVacuousUniversalFresh PASoundness.PAtoCompactGuardedAllCongruence
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Move two universal binders to one fresh name and lift a pair of K child
implications under the retained hypothesis. `vacuity` allows generalizing that
hypothesis at the common name. All binder and name-freshness conditions are
explicit; the child implications are not constructed by this theorem. -/
def guarded_raw_align (p q z base : Nat) (f g : Formula) (H : Nat)
    (hpz : p < z) (hqz : q < z) (hzbase : z < base)
    (hp : p ∉ f.binders) (hq : q ∉ g.binders)
    (hzf : z ∉ f.names) (hzg : z ∉ g.names)
    (vacuity : KDerivation (imp H (allCode z H)))
    (forward : KDerivation (imp H (imp (replace p z f).encode (replace q z g).encode)))
    (backward : KDerivation (imp H (imp (replace q z g).encode (replace p z f).encode))) :
    KDerivation (imp H (imp (rawGuard p f).encode (rawGuard q g).encode)) ×
      KDerivation (imp H (imp (rawGuard q g).encode (rawGuard p f).encode)) := by
  have hpbase : p < base := by omega
  have hqbase : q < base := by omega
  have hpf : z ∉ (.imp (domainAt base p) f : Formula).names := by
    simp only [Formula.names, Finset.mem_union, not_or]
    exact ⟨low_name_not_domain_names base p z (by omega) (by omega), hzf⟩
  have hqg : z ∉ (.imp (domainAt base q) g : Formula).names := by
    simp only [Formula.names, Finset.mem_union, not_or]
    exact ⟨low_name_not_domain_names base q z (by omega) (by omega), hzg⟩
  have ra := raw_rebase p base f (by omega)
  have rb := raw_rebase q base g (by omega)
  have aa := raw_high_alpha p z base f hpbase (by omega) hp hpf
  have ba := raw_high_alpha q z base g hqbase (by omega) hq hqg
  let D := (domainAt base z).encode
  let A := (replace p z f).encode
  let B := (replace q z g).encode
  have addDomain {X Y : Nat} (h : KDerivation (imp H (imp X Y))) :
      KDerivation (imp H (imp D (imp X Y))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [X, D, H]
    have hX : Context Γ X := Context.head _ _
    have hH : Context Γ H := .hypothesis (by simp [Γ])
    exact .mp hX (.mp hH (.closed h))
  have hi := guarded_all_both z H D A B vacuity (addDomain forward) (addDomain backward)
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(rawGuard p f).encode, H]
    have hh : Context Γ H := .hypothesis (by simp [Γ])
    have hf : Context Γ (rawGuard p f).encode := Context.head _ _
    have ha := Context.mp (Context.mp hf (.closed ra.1)) (.closed aa.forward)
    have hb := Context.mp ha (Context.mp hh (.closed hi.1))
    exact .mp (.mp hb (.closed ba.backward)) (.closed rb.2)
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(rawGuard q g).encode, H]
    have hh : Context Γ H := .hypothesis (by simp [Γ])
    have hg : Context Γ (rawGuard q g).encode := Context.head _ _
    have hb := Context.mp (Context.mp hg (.closed rb.1)) (.closed ba.forward)
    have ha := Context.mp hb (Context.mp hh (.closed hi.2))
    exact .mp (.mp ha (.closed aa.backward)) (.closed ra.2)

/-- A syntactically fresh common binder supplies the vacuity proof. The
caller may choose a binder above both child-name sets and H's free support. -/
def guarded_raw_align_of_free (p q z base : Nat) (f g H : Formula)
    (hpz : p < z) (hqz : q < z) (hzbase : z < base)
    (hp : p ∉ f.binders) (hq : q ∉ g.binders)
    (hzf : z ∉ f.names) (hzg : z ∉ g.names) (hzH : z ∉ H.free)
    (forward : KDerivation (imp H.encode (imp (replace p z f).encode (replace q z g).encode)))
    (backward : KDerivation (imp H.encode (imp (replace q z g).encode (replace p z f).encode))) :
    KDerivation (imp H.encode (imp (rawGuard p f).encode (rawGuard q g).encode)) ×
      KDerivation (imp H.encode (imp (rawGuard q g).encode (rawGuard p f).encode)) :=
  guarded_raw_align p q z base f g H.encode hpz hqz hzbase hp hq hzf hzg
    (free_vacuity z H hzH) forward backward

end PASoundness.PAtoCompactGuardedUniversalAlignment

#print axioms PASoundness.PAtoCompactGuardedUniversalAlignment.guarded_raw_align
#print axioms PASoundness.PAtoCompactGuardedUniversalAlignment.guarded_raw_align_of_free
