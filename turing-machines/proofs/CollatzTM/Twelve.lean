import CollatzTM.Machine12

namespace CollatzTM.M12

abbrev Stream := Nat → Bool

def zeros : Stream := fun _ => false

def cons (b : Bool) (s : Stream) : Stream
  | 0 => b
  | n+1 => s n

def tail (s : Stream) : Stream := fun n => s (n+1)

@[simp] theorem cons_zero (b : Bool) (s : Stream) : cons b s 0 = b := rfl
@[simp] theorem cons_succ (b : Bool) (s : Stream) (n : Nat) : cons b s (n+1) = s n := rfl
@[simp] theorem tail_cons (b : Bool) (s : Stream) : tail (cons b s) = s := rfl
@[simp] theorem tail_zeros : tail zeros = zeros := rfl
@[simp] theorem cons_false_zeros : cons false zeros = zeros := by
  funext n; cases n <;> rfl

def absTape (p : Int) (l r : Stream) : Tape := fun z =>
  if z < p then l (p-z-1).toNat else r (z-p).toNat

def cfg (q : Option State) (p : Int) (l r : Stream) : Config State :=
  ⟨q, p, absTape p l r⟩

@[simp] theorem absTape_here (p : Int) (l r : Stream) : absTape p l r p = r 0 := by
  simp [absTape]

theorem tape_right (p : Int) (l r : Stream) (w : Bool) :
    put (absTape p l r) p w = absTape (p+1) (cons w l) (tail r) := by
  funext z
  simp only [put, absTape]
  by_cases e : z = p
  · subst z
    rw [if_pos (by omega : p < p+1)]
    have hn : (p+1-p-1).toNat = 0 := by omega
    rw [hn]; simp only [↓reduceIte, cons_zero]
  · simp only [e, ↓reduceIte]
    by_cases h : z < p
    · have h' : z < p+1 := by omega
      have hnat : (p+1-z-1).toNat = (p-z-1).toNat+1 := by omega
      simp [h, h', hnat]
    · have h' : ¬z < p+1 := by omega
      have hnat : (z-(p+1)).toNat+1 = (z-p).toNat := by omega
      simp [h, h', tail, hnat]

theorem tape_left (p : Int) (l r : Stream) (w : Bool) :
    put (absTape p l r) p w =
      absTape (p-1) (tail l) (cons (l 0) (cons w (tail r))) := by
  funext z
  simp only [put, absTape]
  by_cases e : z = p
  · subst z
    rw [if_neg (by omega : ¬p < p-1)]
    have hn : (p-(p-1)).toNat = 1 := by omega
    rw [hn]; simp only [↓reduceIte, cons_zero, cons_succ]
  · simp only [e, ↓reduceIte]
    by_cases e' : z = p-1
    · subst z
      rw [if_pos (by omega : p-1 < p), if_neg (by omega : ¬p-1 < p-1)]
      have h1 : (p-(p-1)-1).toNat = 0 := by omega
      have h2 : (p-1-(p-1)).toNat = 0 := by omega
      rw [h1, h2]; rfl
    · by_cases h : z < p-1
      · have h' : z < p := by omega
        have hnat : (p-1-z-1).toNat+1 = (p-z-1).toNat := by omega
        simp only [if_pos h, if_pos h', tail]
        rw [hnat]
      · have h' : ¬z < p := by omega
        have hnat : (z-(p-1)).toNat = (z-p).toNat+1 := by omega
        have hpos : 0 < (z-p).toNat := by omega
        cases hn : (z-p).toNat with
        | zero => omega
        | succ n => simp [h, h', hnat, hn, tail]

theorem step_R (q q' : State) (p : Int) (l r : Stream) (w : Bool)
    (h : delta q (r 0) = ⟨w, .R, some q'⟩) :
    step delta (cfg (some q) p l r) = cfg (some q') (p+1) (cons w l) (tail r) := by
  simp only [step, cfg, absTape_here, h, move]
  rw [tape_right]

theorem step_L (q : State) (q' : Option State) (p : Int) (l r : Stream) (w : Bool)
    (h : delta q (r 0) = ⟨w, .L, q'⟩) :
    step delta (cfg (some q) p l r) =
      cfg q' (p-1) (tail l) (cons (l 0) (cons w (tail r))) := by
  simp only [step, cfg, absTape_here, h, move]
  rw [tape_left]
  congr 1 <;> omega

/-- Paired, least-significant-first bits, with blank continuation. -/
def enc : List Bool → Stream
  | [] => zeros
  | b :: bs => cons true (cons b (enc bs))

def canonical (bs : List Bool) (p : Int) : Config State :=
  cfg (some .A) p zeros (enc bs)

def value : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

def Normal (bs : List Bool) : Prop :=
  bs ≠ [] ∧ bs.getLast? = some true


theorem even_pair (bs : List Bool) (p : Int) (l : Stream) :
    run delta 2 (cfg (some .A) p l (enc (false::bs))) =
      cfg (some .A) (p+2) (cons false (cons false l)) (enc bs) := by
  simp only [run]
  rw [step_R .A .K p l (enc (false::bs)) false (by rfl)]
  rw [step_R .K .A (p+1) (cons false l) (tail (enc (false::bs))) false (by rfl)]
  congr 1 <;> first | rfl | omega | simp [enc, tail]

theorem canonical_even (bs : List Bool) (p : Int) :
    Reaches delta 2 (canonical (false::bs) p) (canonical bs (p+2)) := by
  apply reaches_no_early
  · simpa [canonical] using even_pair bs p zeros
  · simp [canonical, cfg]

theorem canonical_one (p : Int) :
    Reaches delta 3 (canonical [true] p) (cfg none (p+1) zeros zeros) := by
  have h2 : run delta 2 (canonical [true] p) =
      cfg (some .L) (p+2) zeros zeros := by
    simp only [canonical, run]
    rw [step_R .A .K p zeros (enc [true]) false (by rfl)]
    rw [step_R .K .L (p+1) (cons false zeros) (tail (enc [true])) false (by rfl)]
    simp [enc]
    congr 1 <;> omega
  have h3 : run delta 3 (canonical [true] p) = cfg none (p+1) zeros zeros := by
    rw [show 3=2+1 from rfl, run_add, h2]
    simp only [run]
    rw [step_L .L none (p+2) zeros zeros false (by rfl)]
    simp [zeros]
    congr 1 <;> omega
  refine ⟨h3, ?_⟩
  intro j hj
  have : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases this with rfl | rfl | rfl
  · simp [run, canonical, cfg]
  · simp only [run, canonical]
    rw [step_R .A .K p zeros (enc [true]) false (by rfl)]
    simp [cfg]
  · rw [h2]; simp [cfg]

inductive Carry where
  | c0 | c1 | c2
  deriving DecidableEq, Repr

def carryState : Carry → State
  | .c0 => .B
  | .c1 => .D
  | .c2 => .F

def digit : Carry → Bool → Bool
  | .c0, b => b
  | .c1, b => !b
  | .c2, b => b

def nextCarry : Carry → Bool → Carry
  | .c0, false => .c0
  | .c0, true => .c1
  | .c1, false => .c0
  | .c1, true => .c2
  | .c2, false => .c1
  | .c2, true => .c2

def carryValue : Carry → Nat
  | .c0 => 0
  | .c1 => 1
  | .c2 => 2

theorem carry_arith (c : Carry) (b : Bool) :
    3*b.toNat+carryValue c = (digit c b).toNat+2*carryValue (nextCarry c b) := by
  cases c <;> cases b <;> decide

def output : Carry → List Bool → List Bool
  | .c0, [] => []
  | .c1, [] => [true]
  | .c2, [] => [false,true]
  | c, b::bs => digit c b :: output (nextCarry c b) bs

inductive Good : Carry → List Bool → Prop
  | nil1 : Good .c1 []
  | nil2 : Good .c2 []
  | cons (c : Carry) (b : Bool) (bs : List Bool) :
      Good (nextCarry c b) bs → Good c (b::bs)

theorem pair_forward (c : Carry) (b : Bool) (bs : List Bool) (p : Int) (l : Stream) :
    run delta 2 (cfg (some (carryState c)) p l (enc (b::bs))) =
      cfg (some (carryState (nextCarry c b))) (p+2)
        (cons (digit c b) (cons true l)) (enc bs) := by
  cases c <;> cases b <;> simp only [carryState, nextCarry, digit, Bool.not_false, Bool.not_true]
  all_goals
    simp only [run]
    rw [step_R _ _ _ _ _ _ (by rfl)]
    rw [step_R _ _ _ _ _ _ (by rfl)]
    congr 1 <;> first | rfl | omega | simp [enc, tail]


def push : List Bool → Stream → Stream
  | [], l => l
  | b::bs, l => push bs (cons b (cons true l))

def appendEnc : List Bool → Stream → Stream
  | [], r => r
  | b::bs, r => cons true (cons b (appendEnc bs r))

@[simp] theorem appendEnc_zeros (bs : List Bool) : appendEnc bs zeros = enc bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [appendEnc, enc, ih]

def endCfg (p : Int) (l : Stream) : Config State :=
  cfg (some .I) (p-2) (tail (tail l)) (cons (l 1) (cons (l 0) zeros))

def finish (bs : List Bool) (p : Int) (l : Stream) : Config State :=
  endCfg (p+2*(bs.length : Int)) (push bs l)

theorem finish_cons (b : Bool) (bs : List Bool) (p : Int) (l : Stream) :
    finish (b::bs) p l = finish bs (p+2) (cons b (cons true l)) := by
  simp only [finish, push, List.length_cons, Int.natCast_add, Int.natCast_one]
  congr 1
  omega

theorem forward (c : Carry) (bs : List Bool) (h : Good c bs) (p : Int) (l : Stream) :
    run delta (2*(output c bs).length)
      (cfg (some (carryState c)) p l (enc bs)) = finish (output c bs) p l := by
  induction h generalizing p l with
  | nil1 =>
    simp only [output, List.length_cons, List.length_nil, run, carryState, enc]
    rw [step_R .D .H p l zeros true (by rfl)]
    rw [step_L .H (some .I) (p+1) (cons true l) (tail zeros) true (by rfl)]
    simp only [finish, endCfg, push, List.length_cons, List.length_nil, cons_zero,
      cons_succ, tail_cons, tail_zeros]
    congr 1 <;> first | rfl | omega
  | nil2 =>
    simp only [output, List.length_cons, List.length_nil, run, carryState, enc]
    rw [step_R .F .B p l zeros true (by rfl)]
    rw [step_R .B .A (p+1) (cons true l) (tail zeros) false (by rfl)]
    rw [step_R .A .H (p+1+1) (cons false (cons true l)) (tail (tail zeros)) true (by rfl)]
    rw [step_L .H (some .I) (p+1+1+1)
      (cons true (cons false (cons true l))) (tail (tail (tail zeros))) true (by rfl)]
    simp only [finish, endCfg, push, List.length_cons, List.length_nil, cons_zero,
      cons_succ, tail_cons, tail_zeros]
    congr 1 <;> first | rfl | omega
  | cons c b bs h ih =>
    have ht : 2*(output c (b::bs)).length = 2+2*(output (nextCarry c b) bs).length := by
      simp [output]; omega
    rw [ht, run_add, pair_forward, ih, output, finish_cons]

theorem appendEnc_head (bs : List Bool) (r : Stream) (h : r 0=true) :
    appendEnc bs r 0 = true := by
  cases bs <;> simp [appendEnc, h]

theorem back_pair (b : Bool) (p : Int) (l r : Stream) (h : r 0=true) :
    run delta 2 (cfg (some .I) (p+2) (cons b (cons true l)) r) =
      cfg (some .I) p l (cons true (cons b r)) := by
  have hr : r = cons true (tail r) := by
    funext n; cases n <;> simp [cons, tail, h]
  simp only [run]
  rw [step_L .I (some .J) (p+2) (cons b (cons true l)) r true (by simp [h, delta])]
  rw [step_L .J (some .I) (p+2-1) (tail (cons b (cons true l)))
    (cons (cons b (cons true l) 0) (cons true (tail r))) b (by cases b <;> rfl)]
  simp only [tail_cons, cons_zero]
  rw [←hr]
  congr 1 <;> first | rfl | omega

theorem back_scan (bs : List Bool) (p : Int) (l r : Stream) (h : r 0=true) :
    run delta (2*bs.length)
      (cfg (some .I) (p+2*(bs.length : Int)) (push bs l) r) =
      cfg (some .I) p l (appendEnc bs r) := by
  induction bs generalizing p l with
  | nil => simp [run, push, appendEnc]
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2*bs.length+2 := by simp; omega
    have hp : p+2*((b::bs).length : Int) = (p+2)+2*(bs.length : Int) := by
      simp; omega
    rw [ht, hp, push, run_add, ih, back_pair b p l _ (appendEnc_head bs r h)]
    rfl


theorem output_value (c : Carry) (bs : List Bool) :
    value (output c bs) = 3*value bs+carryValue c := by
  induction bs generalizing c with
  | nil => cases c <;> decide
  | cons b bs ih =>
    simp only [output, value]
    rw [ih]
    have hc := carry_arith c b
    omega

theorem output_normal (c : Carry) (bs : List Bool) (h : Good c bs) :
    Normal (output c bs) := by
  induction h with
  | nil1 => simp [Normal, output]
  | nil2 => simp [Normal, output]
  | cons c b bs h ih =>
    refine ⟨by simp [output], ?_⟩
    simp only [output, List.getLast?_cons, ih.2, Option.getD_some]

theorem normal_good (c : Carry) (bs : List Bool) (h : Normal bs) : Good c bs := by
  induction bs generalizing c with
  | nil => exact False.elim (h.1 rfl)
  | cons b bs ih =>
    cases bs with
    | nil =>
      have hb : b=true := by simpa [Normal] using h.2
      subst b
      cases c
      · exact .cons .c0 true [] .nil1
      · exact .cons .c1 true [] .nil2
      · exact .cons .c2 true [] .nil2
    | cons b' bs =>
      apply Good.cons
      apply ih
      refine ⟨by simp, ?_⟩
      simpa only [List.getLast?_cons, Option.getD_some] using h.2

theorem push_append (as bs : List Bool) (l : Stream) :
    push (as++bs) l = push bs (push as l) := by
  induction as generalizing l with
  | nil => rfl
  | cons a as ih => exact ih (cons a (cons true l))

theorem appendEnc_append (as bs : List Bool) (r : Stream) :
    appendEnc (as++bs) r = appendEnc as (appendEnc bs r) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [appendEnc, ih]

theorem home (p : Int) (r : Stream) (h : r 0=true) :
    run delta 4 (cfg (some .I) p zeros r) = cfg (some .A) p zeros r := by
  have hr : r=cons true (tail r) := by
    funext n; cases n <;> simp [cons, tail, h]
  simp only [run]
  rw [step_L .I (some .J) p zeros r true (by simp [h, delta])]
  rw [step_L .J (some .I) (p-1) (tail zeros)
    (cons (zeros 0) (cons true (tail r))) false (by rfl)]
  rw [step_R .I .K (p-1-1) (tail (tail zeros))
    (cons (tail zeros 0) (cons false (tail (cons (zeros 0) (cons true (tail r))))))
    false (by rfl)]
  rw [step_R .K .A (p-1-1+1) (cons false (tail (tail zeros)))
    (tail (cons (tail zeros 0) (cons false (tail (cons (zeros 0) (cons true (tail r)))))))
    false (by rfl)]
  simp only [tail_cons, tail_zeros, cons_false_zeros]
  rw [←hr]
  congr 1 <;> first | rfl | omega

theorem finish_return (bs : List Bool) (h : Normal bs) (p : Int) :
    run delta (2*bs.length+2) (finish bs p zeros) = canonical bs p := by
  obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp h.2
  have ht : 2*(pre++[true]).length+2 = 2*pre.length+4 := by simp; omega
  have hf : finish (pre++[true]) p zeros =
      cfg (some .I) (p+2*(pre.length : Int)) (push pre zeros) (enc [true]) := by
    simp only [finish, push_append, endCfg, push, tail_cons, cons_zero, cons_succ]
    congr 1 <;> (try simp) <;> omega
  rw [ht, hf, run_add, back_scan pre p zeros (enc [true]) (by rfl)]
  rw [home p _ (appendEnc_head pre (enc [true]) (by rfl))]
  simp only [canonical]
  congr 1
  rw [←appendEnc_zeros [true], ←appendEnc_append, appendEnc_zeros]

/-- Direct macro theorem on canonical bit strings; every tape cell is accounted for. -/
theorem canonical_odd (bs : List Bool) (h : Normal bs) (p : Int) :
    Reaches delta (4*(output .c2 bs).length+4)
      (canonical (true::bs) p) (canonical (output .c2 bs) (p+2)) := by
  have good := normal_good .c2 bs h
  have init : run delta 2 (canonical (true::bs) p) =
      cfg (some .L) (p+2) zeros (enc bs) := by
    simp only [canonical, run]
    rw [step_R .A .K p zeros (enc (true::bs)) false (by rfl)]
    rw [step_R .K .L (p+1) (cons false zeros) (tail (enc (true::bs))) false (by rfl)]
    simp only [enc, tail_cons, cons_false_zeros]
    congr 1 <;> first | rfl | omega
  have same : step delta (cfg (some .L) (p+2) zeros (enc bs)) =
      step delta (cfg (some .F) (p+2) zeros (enc bs)) := by
    have he : enc bs 0=true := by cases bs with
      | nil => exact False.elim (h.1 rfl)
      | cons b bs => rfl
    simp [step, cfg, he, delta]
  have fwd : run delta (2*(output .c2 bs).length)
      (cfg (some .L) (p+2) zeros (enc bs)) = finish (output .c2 bs) (p+2) zeros := by
    have hn : 0 < 2*(output .c2 bs).length := by
      have ho := (output_normal .c2 bs good).1
      have : 0 < (output .c2 bs).length := List.length_pos_iff.mpr ho
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2*(output .c2 bs).length ≠ 0)
    have ff := forward .c2 bs good (p+2) zeros
    rw [hk, run] at ff ⊢
    rw [same]
    exact ff
  apply reaches_no_early
  · have ht : 4*(output .c2 bs).length+4 =
        2+(2*(output .c2 bs).length+(2*(output .c2 bs).length+2)) := by omega
    rw [ht, run_add, init, run_add, fwd, finish_return _ (output_normal .c2 bs good)]
  · simp [canonical, cfg]


/-- The pair stream has no nonblank cells beyond the encoded word. -/
theorem enc_beyond (bs : List Bool) (n : Nat) (h : 2*bs.length ≤ n) :
    enc bs n = false := by
  induction bs generalizing n with
  | nil => rfl
  | cons b bs ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      cases n with
      | zero => simp at h; omega
      | succ n =>
        exact ih n (by simp at h; omega)

/-- The encoding uses precisely a marker and then a data cell for each bit. -/
theorem enc_pair_at (bs : List Bool) (i : Nat) (h : i < bs.length) :
    enc bs (2*i) = true ∧ enc bs (2*i+1) = bs[i] := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b bs ih =>
    cases i with
    | zero => simp [enc]
    | succ i =>
      have hi : i < bs.length := by simp at h; omega
      have hm : 2*(i+1) = (2*i)+2 := by omega
      have hb : 2*(i+1)+1 = (2*i+1)+2 := by omega
      simpa only [hm, hb, enc, cons_succ, List.getElem_cons_succ] using ih i hi

/-- Every canonical input is a finite-support two-way tape. -/
theorem canonical_finite (bs : List Bool) (p : Int) :
    FiniteTape (canonical bs p).tape := by
  refine ⟨p, p+2*(bs.length : Int), ?_⟩
  intro z hz
  change absTape p zeros (enc bs) z = false
  by_cases h : z < p
  · simp [absTape, h, zeros]
  · rw [absTape, if_neg h]
    apply enc_beyond
    omega

/-- Tail required for an odd input larger than one. -/
theorem normal_tail {b : Bool} {bs : List Bool} (h : Normal (b::bs)) (hne : bs≠[]) :
    Normal bs := by
  refine ⟨hne, ?_⟩
  cases bs with
  | nil => exact False.elim (hne rfl)
  | cons b' bs => simpa only [List.getLast?_cons, Option.getD_some] using h.2

end CollatzTM.M12
