import Std

namespace Lobster

inductive Letter | bare | leaf | arm | fork
  deriving DecidableEq, Repr
inductive State | start | port (rank : Fin 4) | finish
  deriving DecidableEq, Repr

abbrev Rules := State → List Letter → State → Prop

/-- The word index is newest letter first. Rule words are in reading order.
    A derivation is a parse witness, independent of the window algorithm. -/
inductive Parsed (R : Rules) : List Letter → State → Prop where
  | initial : Parsed R [] .start
  | block {pre tail c a b} :
      Parsed R pre a → a ≠ .finish → b ≠ .start → tail.length < 6 →
      R a (c :: tail).reverse b → Parsed R (c :: (tail ++ pre)) b

def Terminal (b : State) := b = .finish ∨ b = .port 0

structure Window where
  recent : List Letter
  hist : Fin 6 → State → Prop

def initial : Window :=
  ⟨[], fun i a => i.val = 0 ∧ a = .start⟩

def Output (R : Rules) (s : Window) (c : Letter) (b : State) : Prop :=
  b ≠ .start ∧ ∃ (i : Fin 6) (a : State),
    i.val ≤ s.recent.length ∧ s.hist i a ∧
    R a (c :: s.recent.take i.val).reverse b

def advance (R : Rules) (s : Window) (c : Letter) : Window :=
  ⟨(c :: s.recent).take 5, fun i a =>
    match i.val with
    | 0 => Output R s c a ∧ a ≠ .finish
    | j+1 => if h : j < 6 then s.hist ⟨j,h⟩ a else False⟩

/-- Inactive slots before the empty prefix are false. -/
def Represents (R : Rules) (s : Window) (w : List Letter) : Prop :=
  s.recent = w.take 5 ∧ ∀ i a, s.hist i a ↔
    i.val ≤ w.length ∧ Parsed R (w.drop i.val) a ∧ a ≠ .finish

theorem initial_correct (R : Rules) : Represents R initial [] := by
  refine ⟨rfl, ?_⟩
  intro i a
  constructor
  · rintro ⟨hi, rfl⟩
    exact ⟨by simp [hi], by simpa using Parsed.initial (R := R), by decide⟩
  · rintro ⟨hi, hp, _⟩
    have hz : i.val = 0 := by simpa using hi
    simp only [List.drop_nil] at hp
    cases hp
    exact ⟨hz, rfl⟩

theorem output_exact {R s w} (hs : Represents R s w) (c b) :
    Output R s c b ↔ Parsed R (c :: w) b := by
  constructor
  · rintro ⟨hb, i, a, _, ha, hr⟩
    obtain ⟨_, hp, hn⟩ := (hs.2 i a).mp ha
    have hi : i.val ≤ 5 := by have := i.isLt; omega
    rw [hs.1, List.take_take, Nat.min_eq_left hi] at hr
    have short : (w.take i.val).length < 6 := by
      simp only [List.length_take]; omega
    simpa only [List.take_append_drop] using
      (Parsed.block hp hn hb short hr)
  · intro hp
    cases hp with
    | @block pre tail _ a _ hp hn hb short hr =>
      let i : Fin 6 := ⟨tail.length, short⟩
      have cut : tail.length ≤ 5 := by omega
      refine ⟨hb, i, a, ?_, ?_, ?_⟩
      · simp only [i, hs.1, List.length_take, List.length_append]; omega
      · apply (hs.2 i a).mpr
        simpa [i, List.drop_append] using And.intro (show tail.length ≤ tail.length + pre.length by omega) (And.intro hp hn)
      · change R a (c :: s.recent.take tail.length).reverse _
        rw [hs.1, List.take_take, Nat.min_eq_left cut, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
        exact hr

theorem advance_correct {R s w} (hs : Represents R s w) (c) :
    Represents R (advance R s c) (c :: w) := by
  constructor
  · simp [advance, hs.1, List.take_succ_cons, List.take_take]
  · intro ⟨i, hi⟩ a
    cases i with
    | zero => simp [advance, output_exact hs]
    | succ j =>
      have hj : j < 6 := by omega
      simpa [advance, hj, List.drop_succ_cons] using hs.2 ⟨j,hj⟩ a

/-- Any closed set with accepting outgoing edges suffices, even if it
    includes extra states. No correctness assumption about BFS is needed. -/
theorem coverage (R : Rules) (C : Window → Prop) (base : C initial)
    (closed : ∀ s, C s → ∀ c, C (advance R s c))
    (accept : ∀ s, C s → ∀ c, ∃ b, Terminal b ∧ Output R s c b)
    (word : List Letter) (nonempty : word ≠ []) :
    ∃ b, Terminal b ∧ Parsed R word.reverse b := by
  have run : ∀ w, ∃ s, C s ∧ Represents R s w := by
    intro w
    induction w with
    | nil => exact ⟨initial, base, initial_correct R⟩
    | cons c w ih =>
      obtain ⟨s, hc, hs⟩ := ih
      exact ⟨advance R s c, closed s hc c, advance_correct hs c⟩
  cases h : word.reverse with
  | nil => simp_all
  | cons c w =>
    obtain ⟨s,hc,hs⟩ := run w
    obtain ⟨b, ht, ho⟩ := accept s hc c
    exact ⟨b, ht, (output_exact hs c b).mp ho⟩

#print axioms Lobster.coverage
end Lobster

