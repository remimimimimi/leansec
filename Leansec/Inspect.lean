import Leansec.Indexed
import Mathlib.Data.Vector

namespace Leansec

namespace Inspect

abbrev View : (Nat → Type) → Type → Nat → Type
  | _, _, 0 => Empty
  | as, a, n+1 => a × as n

end Inspect

class Inspect (as : Nat → Type) (a : Type) where
  inspect : ⟦as ⟶ Option ∘ Inspect.View as a⟧

instance : Inspect (Vector α) α where
  inspect
  | ⟨[], _⟩ => none
  | ⟨x :: xs, h⟩ => some (by
    simp [← h, List.length_cons, Inspect.View]
    exact (x, ⟨xs, rfl⟩)
  )
