import Certificate
import Joining
namespace Lobster
open Geometry

inductive Cell (α : Type u)
  | bare (v : α) | leaf (v h : α) | arm (v h a : α) | fork (v h a b : α)
  deriving DecidableEq, Repr, Inhabited

def Cell.shape : Cell α → Letter
  | .bare _ => .bare | .leaf .. => .leaf | .arm .. => .arm | .fork .. => .fork

def Cell.map (f : α → β) : Cell α → Cell β
  | .bare v => .bare (f v) | .leaf v h => .leaf (f v) (f h)
  | .arm v h a => .arm (f v) (f h) (f a)
  | .fork v h a b => .fork (f v) (f h) (f a) (f b)

def Cell.seg : Cell α → Segment α
  | .bare v => ⟨v,v,[v],[]⟩
  | .leaf v h => ⟨v,v,[v,h],[(v,h)]⟩
  | .arm v h a => ⟨v,v,[v,h,a],[(v,h),(h,a)]⟩
  | .fork v h a b => ⟨v,v,[v,h,a,b],[(v,h),(h,a),(h,b)]⟩

def cat : Option (Segment α) → Option (Segment α) → Option (Segment α)
  | none,b => b | a,none => a | some a,some b => some (join a b)

theorem cat_assoc (a b c : Option (Segment α)) : cat (cat a b) c = cat a (cat b c) := by
  cases a <;> cases b <;> cases c <;> simp [cat,join_assoc]

def strip : List (Cell α) → Option (Segment α)
  | [] => none
  | c::cs => cat (some c.seg) (strip cs)

theorem strip_append (xs ys : List (Cell α)) : strip (xs++ys) = cat (strip xs) (strip ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,strip,ih,cat_assoc]

theorem strip_map (f : α → β) (xs : List (Cell α)) :
    strip (xs.map (Cell.map f)) = (strip xs).map (Segment.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : (x.map f).seg = x.seg.map f := by cases x <;> rfl
    simp only [List.map_cons,strip,ih,h]
    cases strip xs <;> simp [cat]

def Witness (w : List Letter) (s : Segment Nat) : Prop :=
  ∃ xs : List (Cell Nat), xs.map Cell.shape = w ∧ strip xs = some s

theorem witness_map {w s} (h : Witness w s) (f : Nat → Nat) : Witness w (s.map f) := by
  obtain ⟨xs,hw,hs⟩ := h
  refine ⟨xs.map (Cell.map f), ?_, by rw [strip_map,hs]; rfl⟩
  rw [← hw, List.map_map]
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

theorem witness_join {u v s t} (p : Witness u s) (q : Witness v t) :
    Witness (u++v) (join s t) := by
  obtain ⟨xs,hx,hs⟩ := p
  obtain ⟨ys,hy,ht⟩ := q
  exact ⟨xs++ys, by simp [hx,hy], by rw [strip_append,hs,ht]; rfl⟩

def Closed (s : Segment α) : Prop :=
  s.entry ∈ s.nodes ∧ s.exit ∈ s.nodes ∧ ∀ e ∈ s.edges, e.1 ∈ s.nodes ∧ e.2 ∈ s.nodes

theorem cell_closed (c : Cell α) : Closed c.seg := by
  cases c <;> simp [Closed,Cell.seg] <;> grind

theorem join_closed {s t : Segment α} (hs : Closed s) (ht : Closed t) : Closed (join s t) := by
  simp only [Closed,join,List.mem_append,List.mem_singleton] at *
  grind

theorem strip_closed {xs : List (Cell α)} {s} (hs : strip xs = some s) : Closed s := by
  induction xs generalizing s with
  | nil => contradiction
  | cons c cs ih =>
    cases he : strip cs with
    | none =>
      have eq : c.seg = s := by simpa [strip,he,cat] using hs
      exact eq ▸ cell_closed c
    | some t =>
      have eq : join c.seg t = s := by simpa [strip,he,cat] using hs
      exact eq ▸ join_closed (cell_closed c) (ih he)

theorem witness_closed {w s} (hw : Witness w s) : Closed s := by
  obtain ⟨_,_,hs⟩ := hw
  exact strip_closed hs

end Lobster
