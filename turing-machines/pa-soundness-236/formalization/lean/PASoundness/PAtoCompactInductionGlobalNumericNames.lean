import PASoundness.PAtoCompactCandidateRestrictedInduction

/-! Pairwise-distinct labels for the explicit candidate-induction allocation.
This is a finite syntactic arithmetic fact, not a K proof or an induction theorem. -/
namespace PASoundness.PAtoCompactInductionGlobalNumericNames
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Every chosen low name lies below every chosen high name; all displayed
high offsets are pairwise distinct. -/
theorem names_nodup (N B : Nat) (h : N + 101 < B) :
    [N+2, N+1, N+100, N+101, B+5, B+6, B+7, B+8, B+9, B+10, B+11, B+12, B+13, B+14, B+15, B+16, B+17, B+18, B+19, B+20, B+21, B+22, B+23, B+24, B+25, B+26, B+27, B+28, B+29, B+30, B+31, B+32, B+33, B+34, B+35, B+36, B+100, B+101].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true]
  repeat' apply And.intro
  all_goals omega

end PASoundness.PAtoCompactInductionGlobalNumericNames

#print axioms PASoundness.PAtoCompactInductionGlobalNumericNames.names_nodup
