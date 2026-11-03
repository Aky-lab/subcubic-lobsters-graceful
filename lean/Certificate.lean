import Coverage
import Lean.Data.Json
namespace Lobster
deriving instance Hashable for Letter
deriving instance Hashable for State

structure Row where
  src : State
  word : List Letter
  dst : State
  labels : List Nat


private def parseState (n : Int) : Except String State :=
  if n == -1 then pure .start else if n == -2 then pure .finish
  else if h : 0 ≤ n ∧ n.toNat < 4 then pure (.port ⟨n.toNat,h.2⟩)
  else throw "bad port"

private def parseLetter : Char → Except String Letter
  | '0' => pure .bare | 'L' => pure .leaf | 'P' => pure .arm | 'C' => pure .fork
  | _ => throw "bad letter"

def decodeRows (text : String) : Except String (List Row) := do
  let entries ← (← Lean.Json.parse text).getArr?
  entries.toList.mapM fun entry => do
    let fields ← entry.getArr?
    match fields.toList with
    | [a,w,b,f] =>
      return ⟨← parseState (← a.getInt?), ← (← w.getStr?).toList.mapM parseLetter,
              ← parseState (← b.getInt?), ← Lean.fromJson? f⟩
    | _ => throw "expected a four-field row"

def certificate := decodeRows (include_str "subcubic_lobster_rules.json")
def rows := certificate.toOption.getD []

/-- For each vertex give its parent, with the root at index zero.
    The accompanying Boolean is true on the root's colour class. -/
def vertices (r : Row) : Array (Nat × Bool) := Id.run do
  let mut vs := #[]
  for i in [:r.word.length] do
    vs := vs.push (i-1,i%2 == 0)
  for (c,i) in r.word.zipIdx do
    if c != .bare then
      let head := vs.size
      vs := vs.push (i,i%2 != 0)
      if c == .arm || c == .fork then vs := vs.push (head,i%2 == 0)
      if c == .fork then vs := vs.push (head,i%2 == 0)
  if r.src == .start then vs := vs.push (0,false)
  if r.dst == .finish then
    let last := r.word.length-1
    vs := vs.push (last,last%2 != 0)
  return vs

def validRow (r : Row) : Bool := Id.run do
  if r.word.isEmpty || r.word.length > 6 || r.src == .finish || r.dst == .start then return false
  let vs := vertices r
  let f := r.labels.toArray
  if vs.size != f.size then return false
  let n := vs.size
  let last := r.word.length-1
  let start := r.src == .start
  let mut edgeValues := #[]
  for i in [1:n] do
    let x := f[i]!
    let y := f[vs[i]!.1]!
    edgeValues := edgeValues.push (if start then (x-y)+(y-x) else x+y)
  if start then
    if r.labels.mergeSort != List.range n ||
       edgeValues.toList.mergeSort != (List.range (n-1)).map (·+1) then return false
    if let .port b := r.dst then return f[last]! == b.val || f[last]! + b.val + 1 == n
    return true
  if edgeValues.toList.mergeSort != List.range (n-1) then return false
  for side in [true,false] do
    let indices := ((vs.toList.zip r.labels).filter (fun p => p.1.2 == side)).map Prod.snd
    if indices.mergeSort != List.range indices.length then return false
    if vs[last]!.2 == side then
      if let .port b := r.dst then
        if f[last]! + b.val + 1 != indices.length then return false
  if let .port a := r.src then return f[0]! == a.val
  return false

set_option maxRecDepth 100000 in
theorem rows_checked : rows.length = 6104 ∧ rows.all validRow = true := by native_decide

abbrev Table := Std.HashMap (List Letter × State) (List State)
def addRow (t : Table) (r : Row) : Table :=
  t.insert (r.word,r.src) (r.dst :: t.getD (r.word,r.src) [])
def table := rows.foldl addRow ({} : Table)
def tableRules : Rules := fun a w b => b ∈ table.getD (w,a) []

structure Frame where
  recent : List Letter
  history : List (List State)
  deriving DecidableEq, Hashable, Inhabited

def root : Frame := ⟨[], [[.start]]⟩

def Frame.view (f : Frame) : Window :=
  ⟨f.recent, fun i a => a ∈ f.history[i.val]?.getD []⟩

def ends (f : Frame) (c : Letter) : List State :=
  (List.finRange 6).flatMap fun i =>
    if i.val ≤ f.recent.length then
      (f.history[i.val]?.getD []).flatMap fun a =>
        (table.getD ((c :: f.recent.take i.val).reverse,a) []).filter (· != .start)
    else []

private theorem mem_if {α : Type} (p : Prop) [Decidable p] (l : List α) (x : α) :
    x ∈ (if p then l else []) ↔ p ∧ x ∈ l := by by_cases h : p <;> simp [h]

theorem ends_exact (f : Frame) (c : Letter) (b : State) :
    b ∈ ends f c ↔ Output tableRules f.view c b := by
  simp only [ends, List.mem_flatMap, List.mem_finRange, true_and, mem_if,
    List.mem_filter, bne_iff_ne, Output, Frame.view, tableRules]
  grind

def ports : List State := (List.finRange 4).map State.port
def child (f : Frame) (c : Letter) (out : List State) : Frame :=
  ⟨(c :: f.recent).take 5, ports.filter (fun b => out.contains b) :: f.history.take 5⟩

theorem child_view (f : Frame) (c : Letter) :
    (child f c (ends f c)).view = advance tableRules f.view c := by
  unfold Frame.view advance
  congr 1
  funext ⟨i, hi⟩ a
  apply propext
  cases i with
  | zero =>
    cases a with
    | port b => simp [child, Frame.view, ports, ends_exact]
    | start =>
      simp [child, ports, Output]
    | finish => simp [child, ports]
  | succ j =>
    have hj : j < 5 := by omega
    have hj' : j < 6 := by omega
    simp [child, hj, hj']

theorem root_view : root.view = initial := by
  unfold Frame.view initial
  congr 1
  funext ⟨i,_⟩ a
  cases i <;> simp [root]




def letters : List Letter := [.bare, .leaf, .arm, .fork]
theorem mem_letters (c : Letter) : c ∈ letters := by cases c <;> decide

abbrev Frames := Std.HashSet Frame

/-- Bounded discovery only proposes an invariant. The subsequent check tests
    all outgoing edges afresh, so even an insufficient bound cannot certify it. -/
def discover (fuel : Nat) (seen : Frames) (layer : Array Frame) : Frames := Id.run do
  let mut seen := seen
  let mut layer := layer
  for _ in [:fuel] do
    let mut next := #[]
    for f in layer do
      for c in letters do
        let g := child f c (ends f c)
        if !seen.contains g then
          seen := seen.insert g
          next := next.push g
    layer := next
    if layer.isEmpty then break
  return seen

def frames := discover 47 (({} : Frames).insert root) #[root]

def checkEdge (f : Frame) (c : Letter) : Bool :=
  let out := ends f c
  (out.contains .finish || out.contains (.port 0)) && frames.contains (child f c out)

def checked : Bool :=
  frames.size == 278215 && frames.contains root &&
  frames.toList.all (fun f => letters.all (checkEdge f))

theorem concrete_check : checked = true := by native_decide

theorem table_universal (word : List Letter) (hne : word ≠ []) :
    ∃ b, Terminal b ∧ Parsed tableRules word.reverse b := by
  have h := concrete_check
  simp only [checked, Bool.and_eq_true, Std.HashSet.contains_iff_mem,
    List.all_eq_true, Std.HashSet.mem_toList] at h
  have edge {f : Frame} (hf : f ∈ frames) (c : Letter) := h.2 f hf c (mem_letters c)
  apply coverage tableRules (fun s => ∃ f ∈ frames, f.view = s) _ _ _ word hne
  · exact ⟨root, h.1.2, root_view⟩
  · rintro _ ⟨f,hf,rfl⟩ c
    have he := edge hf c
    simp only [checkEdge, Bool.and_eq_true, Std.HashSet.contains_iff_mem] at he
    exact ⟨_, he.2, child_view f c⟩
  · rintro _ ⟨f,hf,rfl⟩ c
    have he := edge hf c
    simp only [checkEdge, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at he
    cases he.1 with
    | inl hf => exact ⟨.finish, Or.inl rfl, (ends_exact ..).mp hf⟩
    | inr hz => exact ⟨.port 0, Or.inr rfl, (ends_exact ..).mp hz⟩

def rowRules : Rules := fun a w b =>
  ∃ r ∈ rows, (r.word,r.src) = (w,a) ∧ r.dst = b ∧ validRow r = true

private theorem lookup_from_rows (rs : List Row) (t : Table) (k : List Letter × State)
    (b : State) (h : b ∈ (rs.foldl addRow t).getD k []) :
    b ∈ t.getD k [] ∨ ∃ r ∈ rs, (r.word,r.src) = k ∧ r.dst = b := by
  induction rs generalizing t with
  | nil => exact Or.inl h
  | cons r rs ih =>
    rcases ih (addRow t r) h with ha | ⟨r',hm,hk,hd⟩
    · simp only [addRow, Std.HashMap.getD_insert] at ha
      split at ha
      next he =>
        have eq : (r.word,r.src) = k := eq_of_beq he
        rw [eq] at ha
        rcases List.mem_cons.mp ha with hd | hm
        · exact Or.inr ⟨r, List.mem_cons_self, eq, hd.symm⟩
        · exact Or.inl hm
      next => exact Or.inl ha
    · exact Or.inr ⟨r', List.mem_cons_of_mem _ hm, hk, hd⟩

theorem lookup_checked {a w b} (h : tableRules a w b) : rowRules a w b := by
  obtain empty | ⟨r,hm,hk,hd⟩ := lookup_from_rows rows {} (w,a) b h
  · simp at empty
  · exact ⟨r,hm,hk,hd,List.all_eq_true.mp rows_checked.2 _ hm⟩

theorem checked_parse {w b} (h : Parsed tableRules w b) : Parsed rowRules w b := by
  induction h with
  | initial => exact .initial
  | block _ hn hb hs hr ih => exact .block ih hn hb hs (lookup_checked hr)

/-- Every nonempty word has a terminal parse. Every block in that parse has
    a witness among the actual JSON rows that passes the local checker. -/
theorem certificate_universal (word : List Letter) (nonempty : word ≠ []) :
    ∃ b, Terminal b ∧ Parsed rowRules word.reverse b := by
  obtain ⟨b, ht, hp⟩ := table_universal word nonempty
  exact ⟨b, ht, checked_parse hp⟩

#print axioms Lobster.rows_checked
#print axioms Lobster.certificate_universal
end Lobster
