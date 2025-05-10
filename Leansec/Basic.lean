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
-- NOTE: Still unfinished
structure TParserT (ε : Type) (an : Type) (m : Type → Type) (α : Type) : Type where
  run : StateT (Position × List an) (ResultT ε m) α

instance [Monad m] : Functor (TParserT ε an m) where
  map f p := ⟨ p.run.map f ⟩

-- @[inline] def StateT.map {σ m α β} [Monad m] (f : α → β) (x : StateT σ m α) :
--   StateT σ m β :=
--   fun s => do
--     let (a, s') ← x s
--     pure (f a, s')

-- instance {σ : Type u} {m : Type u → Type v} [Monad m] : Functor (StateT σ m) where
--   map := StateT.map

-- @[inline] def StateT.pure {σ m α} [mm : Monad m] (a : α) : StateT σ m α :=
--   fun s => mm.pure (a, s)

-- instance {σ : Type u} {m : Type u → Type v} [Monad m] : Pure (StateT σ m) where
--   pure := StateT.pure

-- instance {σ : Type u} {m : Type u → Type v} [mm : Monad m] : Seq (StateT σ m) where
--   seq f x := λ v => mm.seq f.run _
--     -- fun s => do
--     -- let (g, s₁) ← f s
--     -- let (a, s₂) ← x () s₁
--     -- pure (g a, s₂)

-- instance {σ : Type u} {m : Type u → Type v} [Monad m] : Applicative (StateT σ m) := {}

-- instance {σ : Type u} {m : Type u → Type v} [mm : Monad m] :
--   Applicative (StateT σ m) where

--   pure s := sorry

--   seq := sorry
--     -- ⟨fun s => do
--     --   -- run the function‐parser
--     --   let (g, s') ← f.run s
--     --   -- run the argument‐parser
--     --   let (a, s'') ← x.run s'
--     --   -- return the result
--     --   pure (g a, s'')⟩


instance [Monad m] : Applicative (TParserT ε an m) where
  pure a := ⟨ .pure a ⟩
  seq f x := ⟨ Seq.seq f.run (λ _ => (x ()).run) ⟩

instance [Monad m] : Monad (TParserT ε an m) where
  bind p f := ⟨ do
    let a ← p.run
    (f a).run
  ⟩

instance [Monad m] : MonadLift m (TParserT ε an m) where
  monadLift := (⟨·⟩) ∘ StateT.lift ∘ ExceptT.lift

instance [Monad m] [Coe (Position × List an) ε] : Alternative (TParserT ε an m) where
  /- “Empty” parser: soft fail with the current state coerced into `ε`. -/
  failure := ⟨λ s =>
    throw (.soft (↑ s))⟩

  /- Try `p`; on a soft failure (only), reset to `s` and try `q`; hard failures propagate. -/
  orElse p q := ⟨λ s => do
    let m₁ := (p.run.run s).run

    let m₂ :=
      m₁ >>= fun
        | Except.ok pr             => pure (Except.ok pr)
        | Except.error (.soft  _)  => ((q ()).run.run s).run
        | Except.error (.hard e)   => pure (Except.error (.hard e))

    ExceptT.mk m₂
  ⟩

/-- Get current position. -/
def getPosition [Monad m] : TParserT ε an m Position :=
  ⟨do let (pos,_) ← StateT.get; pure pos⟩

/-- Get the list of annotations. -/
def getAnnotations [Monad m] : TParserT ε an m (List an) :=
  ⟨do let (_,as) ← StateT.get; pure as⟩

-- /-- Push one annotation, run a subparser, then pop it. -/
-- def withAnnotation [Monad m] (a : an) (p : TParserT ε an m α) : TParserT ε an m α :=
--   ⟨fun s => do
--     StateT.modifyGet $ fun (pos,as) => (pos, a :: as)
--     let res ← p.run
--     StateT.modify fun (pos, as) => (pos, as.drop 1)
--     pure res
--   ⟩

/-- Record one character update for position. -/
def recordChar [Monad m] (c : Char) : TParserT ε an m Unit :=
  ⟨ fun (pos,as) => do
    let pos' := update c pos
    pure ((), (pos', as))
  ⟩

-- /-- Commit to this branch: turn *all* failures into hard ones. -/
-- def commitT [Monad m] (p : TParserT ε an m α) : TParserT ε an m α :=
--   ⟨ fun s => do
--     let r ← p.run.run s
--     match r with
--     | Except.ok pr      => pure pr
--     | Except.error err  =>
--       match err with
--       | .soft e => Except.throw (.hard e)
--       | .hard e => Except.throw (.hard e)
--   ⟩

-- instance : MonadLift (TParserT ε an) where
--   lift ma := ⟨ fun s => do
--     let a ← ma
--     pure (a, s)
--   ⟩

-- instance [Functor m] : Functor (TParserT ε a m) where
--   map f p := ⟨ Functor.map f p.run ⟩

-- instance [Functor m] : Functor (TParserT e a m) where
--   map f p := ⟨StateT.map f p.run⟩
