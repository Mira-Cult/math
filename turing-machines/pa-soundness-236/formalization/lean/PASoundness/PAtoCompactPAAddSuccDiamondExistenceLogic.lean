import PASoundness.CompactDerivations

/-! Finite K composition for five nested witnesses. Every contextual
vacuity requirement is explicit; this is a proof-data transformer only and
asserts neither existence of its inputs nor a PA axiom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
open PASoundness.CompactProof PASoundness.CompactDerivations
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Eliminate an existential in a context from a pointwise implication,
provided the context and the conclusion are vacuous at the witness name. -/
def contextual_exists_elim {Γ : List Nat} (k a r : Nat)
    (hc : ∀ h, h ∈ Γ → KDerivation (imp h (allCode k h)))
    (hr : KDerivation (imp r (allCode k r)))
    (hp : Context Γ (imp a r)) (he : Context Γ (existsCode k a)) : Context Γ r :=
  Context.existsElim hr (Context.generalize k hc hp) he

/-- Compose the five witness families with a caller-supplied point proof. The
caller must supply every contextual vacuity proof listed below. The conclusion
R may already contain the five bound existentials, but is otherwise arbitrary. -/
def five_witness_compose (x y z m n g T U V B R : Nat)
    (hx : KDerivation (imp g (existsCode x T)))
    (hy : KDerivation (imp g (existsCode y U)))
    (hz : KDerivation (imp T (imp U (existsCode z V))))
    (hmn : KDerivation (imp T (imp U (imp V (existsCode m (existsCode n B))))))
    (point : KDerivation (imp T (imp U (imp V (imp B R)))))
    (vg : ∀ k, k ∈ [x,y,z,m,n] → KDerivation (imp g (allCode k g)))
    (vT : ∀ k, k ∈ [y,z,m,n] → KDerivation (imp T (allCode k T)))
    (vU : ∀ k, k ∈ [z,m,n] → KDerivation (imp U (allCode k U)))
    (vV : ∀ k, k ∈ [m,n] → KDerivation (imp V (allCode k V)))
    (vR : ∀ k, k ∈ [x,y,z,m,n] → KDerivation (imp R (allCode k R))) :
    KDerivation (imp g R) := by
  let Γ3 := [V,U,T,g]
  have hpoint : Context (B :: Γ3) R := by
    have hB : Context (B :: Γ3) B := .head _ _
    have hV : Context (B :: Γ3) V := .hypothesis (by simp [Γ3])
    have hU : Context (B :: Γ3) U := .hypothesis (by simp [Γ3])
    have hT : Context (B :: Γ3) T := .hypothesis (by simp [Γ3])
    exact .mp hB (.mp hV (.mp hU (.mp hT (.closed point))))
  have hNctx : ∀ h, h ∈ Γ3 → KDerivation (imp h (allCode n h)) := by
    intro h hh
    simp only [Γ3,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h0 : h = V
    · subst h; exact vV n (by simp)
    by_cases h1 : h = U
    · subst h; exact vU n (by simp)
    by_cases h2 : h = T
    · subst h; exact vT n (by simp)
    have h3 : h = g := by simpa [h0,h1,h2] using hh
    subst h; exact vg n (by simp)
  have hN : Context (existsCode n B :: Γ3) R := by
    have hAll := Context.generalize n hNctx (Context.deduction hpoint)
    exact Context.existsElim (vR n (by simp)) (Context.under hAll _)
      (Context.head Γ3 (existsCode n B))
  have hMctx : ∀ h, h ∈ Γ3 → KDerivation (imp h (allCode m h)) := by
    intro h hh
    simp only [Γ3,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h0 : h = V
    · subst h; exact vV m (by simp)
    by_cases h1 : h = U
    · subst h; exact vU m (by simp)
    by_cases h2 : h = T
    · subst h; exact vT m (by simp)
    have h3 : h = g := by simpa [h0,h1,h2] using hh
    subst h; exact vg m (by simp)
  have hMN : Context Γ3 (existsCode m (existsCode n B)) := by
    have hV : Context Γ3 V := .hypothesis (by simp [Γ3])
    have hU : Context Γ3 U := .hypothesis (by simp [Γ3])
    have hT : Context Γ3 T := .hypothesis (by simp [Γ3])
    exact .mp hV (.mp hU (.mp hT (.closed hmn)))
  have hR3 : Context Γ3 R :=
    contextual_exists_elim m (existsCode n B) R hMctx (vR m (by simp)) (Context.deduction hN) hMN
  let Γ2 := [U,T,g]
  have hZctx : ∀ h, h ∈ Γ2 → KDerivation (imp h (allCode z h)) := by
    intro h hh
    simp only [Γ2,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h0 : h = U
    · subst h; exact vU z (by simp)
    by_cases h1 : h = T
    · subst h; exact vT z (by simp)
    have h2 : h = g := by simpa [h0,h1] using hh
    subst h; exact vg z (by simp)
  have hZ : Context Γ2 (existsCode z V) := by
    have hU : Context Γ2 U := .hypothesis (by simp [Γ2])
    have hT : Context Γ2 T := .hypothesis (by simp [Γ2])
    exact .mp hU (.mp hT (.closed hz))
  have hR2 : Context Γ2 R :=
    contextual_exists_elim z V R hZctx (vR z (by simp)) (Context.deduction hR3) hZ
  let Γ1 := [T,g]
  have hYctx : ∀ h, h ∈ Γ1 → KDerivation (imp h (allCode y h)) := by
    intro h hh
    simp only [Γ1,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h0 : h = T
    · subst h; exact vT y (by simp)
    have h1 : h = g := by simpa [h0] using hh
    subst h; exact vg y (by simp)
  have hY : Context Γ1 (existsCode y U) := .mp (.hypothesis (by simp [Γ1])) (.closed hy)
  have hR1 : Context Γ1 R :=
    contextual_exists_elim y U R hYctx (vR y (by simp)) (Context.deduction hR2) hY
  let Γ0 := [g]
  have hXctx : ∀ h, h ∈ Γ0 → KDerivation (imp h (allCode x h)) := by
    intro h hh
    have he : h = g := by simpa [Γ0] using hh
    subst h
    exact vg x (by simp)
  have hX : Context Γ0 (existsCode x T) := .mp (.head [] _) (.closed hx)
  have hR0 : Context Γ0 R :=
    contextual_exists_elim x T R hXctx (vR x (by simp)) (Context.deduction hR1) hX
  exact Context.closeEmpty (Context.deduction hR0)

#print axioms five_witness_compose
end PASoundness.PAtoCompactPAAddSuccDiamondExistenceLogic
