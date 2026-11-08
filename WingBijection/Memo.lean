import WingBijection.FullState

namespace WingBijection

/-- Read a finite table by its keys. -/
def tableLookup {X Y : Type*} [DecidableEq X] (x : X) : List (X × Y) → Option Y
  | [] => none
  | (k, v) :: rest => if x = k then some v else tableLookup x rest

theorem tableLookup_map {X Y : Type*} [DecidableEq X] (f : X → Y)
    (xs : List X) (x : X) (hx : x ∈ xs) :
    tableLookup x (xs.map fun k => (k, f k)) = some (f x) := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.map_cons, tableLookup]
    by_cases ha : x = a
    · simp [ha]
    · rw [if_neg ha]
      exact ih ((List.mem_cons.mp hx).resolve_left ha)

/-- Explicit table data keeps the compiler from eta-expanding a function cache and
rebuilding it on every call. -/
structure MemoTable (X Y : Type*) where
  entries : List (X × Y)

/-- Materialize a finite function as data. -/
@[noinline] def tabulate {X Y : Type*} [Enumeration X] (f : X → Y) : MemoTable X Y :=
  ⟨Enumeration.elems.map fun x => (x, f x)⟩

def MemoTable.apply {X Y : Type*} [DecidableEq X] (t : MemoTable X Y)
    (fallback : X → Y) (x : X) : Y :=
  (tableLookup x t.entries).getD (fallback x)

@[simp] theorem tabulate_apply {X Y : Type*} [Enumeration X] [DecidableEq X]
    (f fallback : X → Y) : (tabulate f).apply fallback = f := by
  funext x
  simp only [MemoTable.apply, tabulate,
    tableLookup_map f _ x (Enumeration.complete x), Option.getD_some]


end WingBijection
