import Leansec.Indexed
import Init.Data.Vector

namespace Leansec

namespace Inspect

abbrev View : (Nat → Type) → Type → Nat → Type
  | _, _, 0 => Empty
  | as, a, n+1 => a × as n

end Inspect

class Inspect (as : Nat → Type) (a : Type) where
  inspect : ⟦as ⟶ Option ∘ Inspect.View as a⟧

instance : Inspect (Vector α) α where
  inspect {n} v := v.elimAsList λ l h =>
    match l with
    | [] => none
    | x :: xs => some (by
      simp [List.length_cons] at h
      simp [← h, Inspect.View]
      refine (x, ?_)
      have len_xs : xs.length = n - 1 := by
        calc
          xs.length = xs.length + 1 - 1 := by simp
          _ = n - 1 := by rw[h]
      rw [len_xs]
      exact v.tail
    )
