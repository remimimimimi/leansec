import Leansec.Indexed

import Mathlib.Data.Vector

namespace Leansec

-- TODO: Abstract over Vector and Token type
abbrev Tok := Char
abbrev Toks := Vector Tok

structure Success (α : Type u) (n : Nat) : Type u where
  value : α
  size : Nat
  small : size < n
  leftovers : Toks size

namespace Success
  -- Wrap constructor just to hide s argument, as I found no way to make an implicit structure field.
  def mk' (v : α) {s : Nat} (sm : s < n) (l : Toks s) : Success α n
   := mk v s sm l

  def map (f : α → β) : Success α n → Success β n :=
    λs => {s with value := f s.value}

  def guardM (f : α → Option β) : ⟦Success α ⟶ Option ∘ Success β⟧ :=
    λs => (f s.value).map (λv => s.map (λ _ => v))

  section Lift
    def le_lift (h : m ≤ n) (s : Success α m) : Success α n :=
      {s with small := Nat.le_trans s.small h}

    def lt_lift (h : m < n) (s : Success α m ) : Success α n :=
      le_lift (Nat.le_of_lt h) s
  end Lift

  def and (p : Success α n) (q : Success β p.size) : Success (α × β) n :=
    q.map (λ v => (p.value, v)) |>.lt_lift p.small
end Success

-- NOTE: According to agdarsec Option could be replaced by RawMonadPlus, that
-- seems like Alternative + Monad.
structure Parser (α : Type u) (n : Nat) : Type u where
  run : ∀{m}, m ≤ n → Toks m → Option (Success α m)
