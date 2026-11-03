import Strips
namespace Lobster
open Geometry

def offers (x n b : Nat) := x = b ∨ x+b+1 = n

def rightCap (b : State) : List Letter := if b == .finish then [.bare] else []
def phaseWord (w : List Letter) (b : State) := [.bare] ++ w ++ rightCap b

/-- Decode the row's serialization into actual spine cells. Caps are individual
bare cells. Bumping the high interval later inserts the old labels between
the two classes. All decoded conditions are checked on these cells directly. -/
def rowCells (r : Row) : List (Cell Nat) := Id.run do
  let mut next := r.word.length
  let f := r.labels.toArray
  let vs := vertices r
  let k := (vs.filter (fun v => !v.2)).size
  let val := fun i : Nat =>
    if r.src == .start then f[i]?.getD 0 else
    if (vs[i]?.getD (0,false)).2 then k+f[i]?.getD 0 else k-1-f[i]?.getD 0
  let mut xs := #[]
  for (c,i) in r.word.zipIdx do
    match c with
    | .bare => xs := xs.push (.bare (val i))
    | .leaf => xs := xs.push (.leaf (val i) (val next)); next := next+1
    | .arm => xs := xs.push (.arm (val i) (val next) (val (next+1))); next := next+2
    | .fork => xs := xs.push (.fork (val i) (val next) (val (next+1)) (val (next+2))); next := next+3
  let left := if r.src == .start then [Cell.bare (val next)] else []
  let right := if r.dst == .finish then [Cell.bare (val (next+left.length))] else []
  return left ++ xs.toList ++ right

def cut (r : Row) := ((vertices r).filter fun v => !v.2).size

def baseExit (b : State) (s : Segment Nat) : Prop :=
  match b with
  | .finish => True | .start => False | .port p => offers s.exit s.nodes.length p.val

def newExit (b : State) (s : Segment Nat) (k : Nat) : Prop :=
  match b with
  | .finish => True | .start => False
  | .port p => (s.exit < k ∧ s.exit = p.val) ∨ (k ≤ s.exit ∧ s.exit+p.val+1 = s.nodes.length)

def segmentOf (r : Row) := (strip (rowCells r)).getD default

def rowClaim (r : Row) : Prop :=
  let s := segmentOf r
  let k := cut r
  strip (rowCells r) = some s ∧
  (rowCells r).map Cell.shape = (if r.src == .start then [.bare] else []) ++ r.word ++ rightCap r.dst ∧
  Good s s.nodes.length ∧ 0 < s.nodes.length ∧ k ≤ s.nodes.length ∧
  match r.src with
  | .start => baseExit r.dst s
  | .finish => False
  | .port p => s.entry = k+p.val ∧ (∀ e ∈ s.edges, (e.1 < k ↔ ¬ e.2 < k)) ∧ newExit r.dst s k

instance (r : Row) : Decidable (rowClaim r) := by
  unfold rowClaim Good
  cases r.src <;> cases r.dst <;> simp only [baseExit,newExit,offers] <;> infer_instance

theorem certifiedGeometry : ∀ r ∈ rows, rowClaim r := by
  have h : rows.all (fun r => decide (rowClaim r)) = true := by native_decide
  simpa only [List.all_eq_true,decide_eq_true_eq] using h

def Realized (w : List Letter) (b : State) : Prop :=
  ∃ s : Segment Nat, Witness (phaseWord w b) s ∧ Good s s.nodes.length ∧
    0 < s.nodes.length ∧ baseExit b s

theorem orient {w s n p} (hw : Witness w s) (hg : Good s n)
    (ho : offers s.exit n p) :
    ∃ t, Witness w t ∧ Good t n ∧ t.exit = p := by
  rcases ho with h | h
  · exact ⟨s,hw,hg,h⟩
  · let f := fun x => n-1-x
    have hc := witness_closed hw
    have bounds (v) (hv : v ∈ s.nodes) : v < n := List.mem_range.mp (hg.1.mem_iff.mp hv)
    refine ⟨s.map f, witness_map hw f, complement_good s n hg ?_, ?_⟩
    · intro e he
      exact ⟨bounds _ (hc.2.2 e he).1, bounds _ (hc.2.2 e he).2⟩
    · change n-1-s.exit = p
      omega

theorem start_realized {r : Row} (hr : r ∈ rows) (ha : r.src = .start) :
    Realized r.word r.dst := by
  obtain ⟨hs,hw,hg,hn,_,hx⟩ := certifiedGeometry r hr
  refine ⟨segmentOf r, ⟨rowCells r, ?_,hs⟩,hg,hn,?_⟩
  · simpa [ha,phaseWord] using hw
  · simpa [ha] using hx

theorem extend_realized {r : Row} (hr : r ∈ rows) {p : Fin 4} (ha : r.src = .port p)
    {u : List Letter} (old : Realized u (.port p)) : Realized (u++r.word) r.dst := by
  obtain ⟨s,hw,hg,hn,ho⟩ := old
  obtain ⟨t,ht,gt,et⟩ := orient hw hg ho
  obtain ⟨hs,shape,gb,nb,hk,spec⟩ := certifiedGeometry r hr
  rw [ha] at spec
  obtain ⟨entry,cross,ex⟩ := spec
  let v := segmentOf r
  let k := cut r
  let n := s.nodes.length
  let B := v.nodes.length
  have eqB : k+(B-k) = B := by dsimp [k,B,v]; omega
  let result := join (t.map (shift k)) (v.map (bump k n))
  have len : result.nodes.length = n+B := by
    have := gt.1.length_eq
    simp [result,join,Segment.map,n,B] at *
    omega
  refine ⟨result, ?_, ?_, ?_, ?_⟩
  · have hv : Witness (r.word ++ rightCap r.dst) v := ⟨rowCells r,by simpa [ha] using shape,hs⟩
    simpa [phaseWord,rightCap,List.append_assoc] using
      witness_join (witness_map ht (shift k)) (witness_map hv (bump k n))
  · rw [len,← eqB]
    exact join_good _ _ n k (B-k) p.val gt (by rw [eqB]; exact gb) hn (by rw [eqB]; exact nb) et entry cross
  · rw [len]; dsimp [n]; omega
  · cases eb : r.dst with
    | finish => trivial
    | start => simp [eb,newExit] at ex
    | port q =>
      rw [eb] at ex
      change offers (bump k n v.exit) result.nodes.length q.val
      rw [len]
      change (v.exit < k ∧ _) ∨ (k ≤ v.exit ∧ _) at ex
      rcases ex with ⟨hl,he⟩ | ⟨hl,he⟩
      · exact Or.inl (by simpa [bump,hl] using he)
      · apply Or.inr
        simp [bump, Nat.not_lt.mpr hl]
        change v.exit + q.val + 1 = B at he
        omega

theorem parse_realized {w b} (hp : Parsed rowRules w b) :
    (b = .start ∧ w = []) ∨ Realized w.reverse b := by
  induction hp with
  | initial => exact Or.inl ⟨rfl,rfl⟩
  | @block pre tail c a b _ hn _ _ rule ih =>
    obtain ⟨r,hr,hk,hd,_⟩ := rule
    have hw := congrArg Prod.fst hk
    have ha := congrArg Prod.snd hk
    change r.word = (c::tail).reverse at hw
    change r.src = a at ha
    subst b
    apply Or.inr
    rcases ih with ⟨rfl,rfl⟩ | prev
    · simpa [hw] using start_realized hr ha
    · cases a with
      | finish => contradiction
      | start =>
        obtain ⟨_,_,_,_,impossible⟩ := prev
        exact False.elim impossible
      | port p =>
        simpa [hw,List.append_assoc] using extend_realized hr ha prev

def singletonCap := (Cell.bare 0).seg

theorem close_zero {w} (h : Realized w (.port 0)) :
    ∃ s, Witness ([.bare] ++ w ++ [.bare]) s ∧ Good s s.nodes.length := by
  obtain ⟨s,hw,hg,hn,ho⟩ := h
  obtain ⟨t,ht,gt,et⟩ := orient hw hg ho
  let n := s.nodes.length
  have hc : Witness [.bare] singletonCap := ⟨[Cell.bare 0],rfl,rfl⟩
  let final := join (t.map (shift 0)) (singletonCap.map (bump 0 n))
  refine ⟨final, ?_, ?_⟩
  · simpa [phaseWord,rightCap] using
      witness_join (witness_map ht (shift 0)) (witness_map hc (bump 0 n))
  · have len := gt.1.length_eq
    have eq : final.nodes.length = n+1 := by
      simp [final,join,Segment.map,singletonCap,Cell.seg,n] at *
      omega
    rw [eq]
    exact join_good t singletonCap n 0 1 0 gt (by unfold Good lengths singletonCap Cell.seg; decide) hn (by decide) et rfl
      (by simp [singletonCap,Cell.seg])

/-- A concrete, globally graceful labeling for every nonempty encoded spine. -/
theorem graceful_word (w : List Letter) (ne : w ≠ []) :
    ∃ s, Witness ([.bare] ++ w ++ [.bare]) s ∧ Good s s.nodes.length := by
  obtain ⟨b,hb,hp⟩ := certificate_universal w ne
  rcases parse_realized hp with ⟨rfl,_⟩ | hr
  · cases hb <;> contradiction
  · rw [List.reverse_reverse] at hr
    rcases hb with rfl | rfl
    · obtain ⟨s,hw,hg,_,_⟩ := hr
      exact ⟨s,hw,hg⟩
    · exact close_zero hr

end Lobster
