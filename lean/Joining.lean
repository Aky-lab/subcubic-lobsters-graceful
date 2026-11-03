import Std
namespace Lobster.Geometry

/-- Ordered vertices and oriented representatives of the undirected edges.
    The two distinguished vertices are the spine interfaces. -/
structure Segment (α : Type u) where
  entry : α
  exit : α
  nodes : List α
  edges : List (α × α)
  deriving DecidableEq, Repr, Inhabited

def Segment.map (f : α → β) (s : Segment α) : Segment β :=
  ⟨f s.entry, f s.exit, s.nodes.map f, s.edges.map (Prod.map f f)⟩

def join (s t : Segment α) : Segment α :=
  ⟨s.entry,t.exit,s.nodes ++ t.nodes,s.edges ++ [(s.exit,t.entry)] ++ t.edges⟩

@[simp] theorem map_join (f : α → β) (s t : Segment α) :
    (join s t).map f = join (s.map f) (t.map f) := by
  simp [join, Segment.map, Prod.map]

theorem join_assoc (s t u : Segment α) : join (join s t) u = join s (join t u) := by
  simp [join, List.append_assoc]

def gap (p : Nat × Nat) := (p.1-p.2)+(p.2-p.1)
def lengths (s : Segment Nat) := s.edges.map gap
def Good (s : Segment Nat) (n : Nat) : Prop :=
  s.nodes.Perm (List.range n) ∧ (lengths s).Perm (List.range' 1 (n-1))

def shift (k : Nat) (x : Nat) := k+x
def bump (k n : Nat) (x : Nat) := if x < k then x else x+n

private theorem shifted (k s m : Nat) :
    (List.range' s m).map (shift k) = List.range' (k+s) m :=
  List.map_add_range' ..

private theorem bump_interval (k n h : Nat) :
    (List.range (k+h)).map (bump k n) =
    List.range' 0 k ++ List.range' (k+n) h := by
  rw [List.range_eq_range', ← List.range'_append_1]
  simp only [Nat.zero_add, List.map_append]
  congr 1
  · apply Eq.trans (b := (List.range' 0 k).map id)
    · apply List.map_congr_left
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_range'.mp hx
      simp [bump,hi]
    · simp
  · apply Eq.trans (b := (List.range' k h).map (shift n))
    · apply List.map_congr_left
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_range'.mp hx
      simp [shift,bump,Nat.add_comm]; omega
    · rw [shifted, Nat.add_comm]

theorem join_good (s t : Segment Nat) (n k h a : Nat)
    (old : Good s n) (new : Good t (k+h)) (hn : 0 < n) (hb : 0 < k+h)
    (left : s.exit = a) (right : t.entry = k+a)
    (cross : ∀ p ∈ t.edges, (p.1 < k) ↔ ¬ (p.2 < k)) :
    Good (join (s.map (shift k)) (t.map (bump k n))) (n+(k+h)) := by
  constructor
  · change ((s.nodes.map _) ++ (t.nodes.map _)).Perm _
    refine ((old.1.map _).append (new.1.map _)).trans ?_
    rw [bump_interval, List.range_eq_range', shifted, Nat.add_zero]
    rw [← List.append_assoc]
    apply (List.Perm.append_right _ List.perm_append_comm).trans
    rw [show List.range' k n = List.range' (0+k) n by simp,
        List.range'_append_1, show List.range' (k+n) h = List.range' (0+(k+n)) h by simp, List.range'_append_1]
    simp [List.range_eq_range', Nat.add_comm, Nat.add_left_comm]
  · have oldEdges : lengths (s.map (shift k)) = lengths s := by
      simp [lengths, Segment.map, List.map_map, Function.comp_def, Prod.map, gap, shift]
      intros; omega
    have newEdges : lengths (t.map (bump k n)) = (lengths t).map (shift n) := by
      simp only [lengths, Segment.map, List.map_map]
      apply List.map_congr_left
      intro p hp
      have hc := cross p hp
      simp only [Function.comp_apply, Prod.map, gap, shift, bump]
      split <;> split <;> omega
    have bridge : gap (shift k s.exit,bump k n t.entry) = n := by
      simp [left,right,gap,shift,bump,show ¬ k+a < k by omega]
    change (((s.map _).edges ++ [(_, _)] ++ (t.map _).edges).map gap).Perm _
    simp only [List.map_append, List.map_cons, List.map_nil]
    change ((lengths (s.map _) ++ [gap (shift k s.exit,bump k n t.entry)]) ++ lengths (t.map _)).Perm _
    rw [oldEdges,newEdges,bridge]
    apply (((old.2.append_right [n]).append (new.2.map _))).trans
    rw [shifted, show [n] = [1+(n-1)] by congr 1; omega, ← List.range'_1_concat]
    rw [show n+1 = 1+(n-1+1) by omega, List.range'_append_1]
    rw [show n-1+1+(k+h-1) = n+(k+h)-1 by omega]

theorem complement_good (s : Segment Nat) (n : Nat) (g : Good s n)
    (bounded : ∀ p ∈ s.edges, p.1 < n ∧ p.2 < n) :
    Good (s.map (fun x => n-1-x)) n := by
  constructor
  · apply (g.1.map _).trans
    have e := List.reverse_range' (s := 0) (n := n)
    simp only [Nat.zero_add, ← List.range_eq_range'] at e
    rw [← e]
    exact List.reverse_perm _
  · unfold lengths
    simp only [Segment.map, List.map_map]
    apply List.Perm.trans (l₂ := lengths s) _ g.2
    apply List.Perm.of_eq
    unfold lengths
    apply List.map_congr_left
    intro p hp
    have := bounded p hp
    simp [gap, Prod.map]; omega

end Lobster.Geometry
