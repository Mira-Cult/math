import PASoundness.PAtoCompactMultiplicationMixedLexLogic

/-! A pointwise order-preservation ingredient for comparing two product
graphs. The factor comparisons and the two product lex comparisons are
explicit K antecedents. This does not collect the matching graph, prove factor
isomorphisms, or establish multiplication functionality or congruence. -/
namespace PASoundness.PAtoCompactProductIsoPointwiseLex

open PASoundness.CompactProof PASoundness.CompactDerivations

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def iffCode (p q : Nat) : Nat := both (imp p q) (imp q p)
def lexCode (major eqMinor minor : Nat) : Nat := either major (both eqMinor minor)

/-- Transport one lexicographic comparison from three pointwise implications.
The equality and both order comparisons remain explicit antecedents. -/
def lex_forward (a a' e e' b b' : Nat) : KDerivation
    (imp (imp a a') (imp (imp e e') (imp (imp b b')
      (imp (lexCode a e b) (lexCode a' e' b'))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [lexCode a e b, imp b b', imp e e', imp a a']
  have hl : Context Γ (either a (both e b)) := by
    simpa [Γ, lexCode] using (Context.head [imp b b', imp e e', imp a a'] (lexCode a e b))
  have ha : Context Γ (imp a a') := .hypothesis (by simp [Γ])
  have he : Context Γ (imp e e') := .hypothesis (by simp [Γ])
  have hb : Context Γ (imp b b') := .hypothesis (by simp [Γ])
  change Context Γ (either a' (both e' b'))
  apply Context.disjunctionElim hl
  · have h : Context (a :: Γ) a := .head _ _
    exact Context.disjunctionLeft (.mp h (.under ha _))
  · have h : Context (both e b :: Γ) (both e b) := .head _ _
    have he' : Context (both e b :: Γ) e' :=
      .mp (Context.conjunctionLeft h) (.under he _)
    have hb' : Context (both e b :: Γ) b' :=
      .mp (Context.conjunctionRight h) (.under hb _)
    exact Context.disjunctionRight (Context.conjunctionIntro he' hb')

/-- If the factor order/equality comparisons correspond and each output
comparison is equivalent to its own lex comparison, the output comparisons
correspond. All five assumptions are literal K antecedents. -/
def pointwise_order (a a' e e' b b' p p' : Nat) : KDerivation
    (imp (iffCode a a') (imp (iffCode e e') (imp (iffCode b b')
      (imp (iffCode p (lexCode a e b))
        (imp (iffCode p' (lexCode a' e' b')) (iffCode p p')))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [iffCode p' (lexCode a' e' b'), iffCode p (lexCode a e b),
    iffCode b b', iffCode e e', iffCode a a']
  have hp' : Context Γ (both (imp p' (lexCode a' e' b'))
      (imp (lexCode a' e' b') p')) := by
    simpa [Γ, iffCode] using
      (Context.head [iffCode p (lexCode a e b), iffCode b b', iffCode e e', iffCode a a']
        (iffCode p' (lexCode a' e' b')))
  have hp : Context Γ (both (imp p (lexCode a e b)) (imp (lexCode a e b) p)) := by
    have h : Context Γ (iffCode p (lexCode a e b)) := .hypothesis (by simp [Γ])
    simpa [iffCode] using h
  have hb : Context Γ (both (imp b b') (imp b' b)) := by
    have h : Context Γ (iffCode b b') := .hypothesis (by simp [Γ])
    simpa [iffCode] using h
  have he : Context Γ (both (imp e e') (imp e' e)) := by
    have h : Context Γ (iffCode e e') := .hypothesis (by simp [Γ])
    simpa [iffCode] using h
  have ha : Context Γ (both (imp a a') (imp a' a)) := by
    have h : Context Γ (iffCode a a') := .hypothesis (by simp [Γ])
    simpa [iffCode] using h
  have hlex : Context Γ (imp (lexCode a e b) (lexCode a' e' b')) :=
    .mp (Context.conjunctionLeft hb) (.mp (Context.conjunctionLeft he)
      (.mp (Context.conjunctionLeft ha) (.closed (lex_forward a a' e e' b b'))))
  have hlex' : Context Γ (imp (lexCode a' e' b') (lexCode a e b)) :=
    .mp (Context.conjunctionRight hb) (.mp (Context.conjunctionRight he)
      (.mp (Context.conjunctionRight ha) (.closed (lex_forward a' a e' e b' b))))
  change Context Γ (both (imp p p') (imp p' p))
  apply Context.conjunctionIntro
  · apply Context.deduction
    have h : Context (p :: Γ) p := .head _ _
    have hl : Context (p :: Γ) (lexCode a e b) :=
      .mp h (.under (Context.conjunctionLeft hp) _)
    have hl' : Context (p :: Γ) (lexCode a' e' b') := .mp hl (.under hlex _)
    exact .mp hl' (.under (Context.conjunctionRight hp') _)
  · apply Context.deduction
    have h : Context (p' :: Γ) p' := .head _ _
    have hl' : Context (p' :: Γ) (lexCode a' e' b') :=
      .mp h (.under (Context.conjunctionLeft hp') _)
    have hl : Context (p' :: Γ) (lexCode a e b) := .mp hl' (.under hlex' _)
    exact .mp hl (.under (Context.conjunctionRight hp) _)

/-- Instantiation at two arbitrary coordinate pairs and two output pairs.
No distinctness assumptions on names or represented values are made. -/
def product_edge_order (a a' b b' A A' B B' o o' O O' : Nat) : KDerivation
    (imp (iffCode (member a' a) (member A' A))
      (imp (iffCode (equal a a') (equal A A'))
        (imp (iffCode (member b' b) (member B' B))
          (imp (iffCode (member o' o)
            (lexCode (member a' a) (equal a a') (member b' b)))
            (imp (iffCode (member O' O)
              (lexCode (member A' A) (equal A A') (member B' B)))
              (iffCode (member o' o) (member O' O))))))) :=
  pointwise_order (member a' a) (member A' A) (equal a a') (equal A A')
    (member b' b) (member B' B) (member o' o) (member O' O)

theorem product_edge_order_certificate (a a' b b' A A' B B' o o' O O' : Nat) :
    theoremCode (certificate (product_edge_order a a' b b' A A' B B' o o' O O')) =
      imp (iffCode (member a' a) (member A' A))
        (imp (iffCode (equal a a') (equal A A'))
          (imp (iffCode (member b' b) (member B' B))
            (imp (iffCode (member o' o)
              (lexCode (member a' a) (equal a a') (member b' b)))
              (imp (iffCode (member O' O)
                (lexCode (member A' A) (equal A A') (member B' B)))
                (iffCode (member o' o) (member O' O)))))) := certificate_correct _

end PASoundness.PAtoCompactProductIsoPointwiseLex

#print axioms PASoundness.PAtoCompactProductIsoPointwiseLex.lexCode
#print axioms PASoundness.PAtoCompactProductIsoPointwiseLex.iffCode
#print axioms PASoundness.PAtoCompactProductIsoPointwiseLex.lex_forward
#print axioms PASoundness.PAtoCompactProductIsoPointwiseLex.pointwise_order
#print axioms PASoundness.PAtoCompactProductIsoPointwiseLex.product_edge_order
#print axioms PASoundness.PAtoCompactProductIsoPointwiseLex.product_edge_order_certificate
