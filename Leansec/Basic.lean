import Leansec.Inspect
import Leansec.Span

namespace Leansec
open Span

/--
A successful partial parse of an A is a value A together leftovers
which are proven to be smaller than the input
-/
structure Success (Toks : Nat → Type) (α : Type) (n : Nat) : Type where
  value : α
  {size : Nat}
  small : size < n
  leftovers : Toks size

namespace Success
  def complete (s : Success τ α n) : Option α :=
     if Success.size s = 0 then s.value else none

  def map (f : α → β) : Success τ α n → Success τ β n :=
    λs => {s with value := f s.value}

  def guardM (f : α → Option β) : ⟦Success τ α ⟶ Option ∘ Success τ β⟧ :=
    λs => (f s.value).map (λv => s.map (λ _ => v))

  section Lift
    def le_lift (h : m ≤ n) (s : Success τ α m) : Success τ α n :=
      {s with small := Nat.le_trans s.small h}

    def lt_lift (h : m < n) (s : Success τ α m) : Success τ α n :=
      le_lift (Nat.le_of_lt h) s
  end Lift

  def and (p : Success τ α n) (q : Success τ β p.size) : Success τ (α × β) n :=
    q.map (λ v => (p.value, v)) |>.lt_lift p.small
end Success

namespace Inspect
  def toSuccess : ⟦View τ τ' ⟶ Success τ τ'⟧
    | 0, v => by contradiction
    | n + 1, ⟨v, vs⟩ => Success.mk v (by simp) vs
end Inspect

namespace Success
  def getTok [Inspect τ τ'] : ⟦τ ⟶ Option ∘ Success τ τ'⟧ :=
    Option.map Inspect.toSuccess ∘ Inspect.inspect
end Success


inductive Fail (ε : Type) where
  | soft : ε → Fail ε
  | hard : ε → Fail ε
deriving Repr, DecidableEq


abbrev Result (ε α) := Except (Fail ε) α
abbrev ResultT (ε m α) := ExceptT (Fail ε) m α

-- TODO: Think about putting m inside parameters.
structure Parser.Parameters (m : Type → Type) where
  -- Type of tokens
  Tok : Type
  -- Type of sized input (like Vector α)
  Toks : Nat → Type
  -- Function that helps us track consumed tokens
  recordToken : Tok → m Unit

structure Parser (mn : Type → Type) (p : Parser.Parameters mn) (α : Type) (n : Nat) : Type where
  run : ∀{m}, m ≤ n → p.Toks m → mn (Success p.Toks α m)

-- TODO: https://github.com/gallais/idris-tparsec/blob/75b288719b9781273a595c294b7d3bed5ea1904d/src/TParsec/Types.idr#L52-L116
-- structure TParserT {p : c → Bool} (ε : Type) (an : Type) (m : Type → Type) (α : Type) where
--   run : StateT (Position p × List an) (ResultT ε m) α
