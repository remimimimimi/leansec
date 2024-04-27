-- TODO: Transit to pattern matching definition of functions like in Agda.
import Leansec.Induction
import Leansec.Basic
import Leansec.Utils

-- There's no nonempty list type in Std, so...
-- It's time for FreeSemigroups? yay
import Mathlib.Algebra.Free

namespace Leansec.Combinators

open Function
open Leansec.Induction

namespace Transitions
  def le_lower : m ≤ n → Parser mn ρ α n → Parser mn ρ α m
    | mlen, ⟨p⟩ => ⟨λ plem => p (Nat.le_trans plem mlen)⟩

  def lt_lower : m < n → Parser mn ρ α n → Parser mn ρ α m
    | mltn => le_lower (Nat.le_of_lt mltn)
end Transitions

def box : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ α ⟧ :=
  Box.Transitions.le_close (λ_ _ => Transitions.le_lower)

instance : Coe (Parser mn ρ α n) ((□ Parser mn ρ α) n) where
  coe := box

-- TODO: Implement combinators as instances of corresponding type classes to
-- avoid ambiguity in notation. Understand how to implement Functor and other
-- type classes for indexed types, because typechecker fails when flipping
-- happing.
--
-- If we could do it, then we can get rid of some of new notation declaration as
-- they're already defined in `Init` library.
section Combinators
  variable
    {ρ : Parser.Parameters mn}

  section
    variable
      [Monad mn] [Alternative mn]

    def guardm (f : α → Option β) : ⟦ Parser mn ρ α ⟶ Parser mn ρ β ⟧
      | _, ⟨p⟩ => Parser.mk λ mltn ts => do
        let s ← p mltn ts
        Success.guardM f s |>.elim failure pure

    def guard : (α → Bool) → ⟦ Parser mn ρ α ⟶ Parser mn ρ α ⟧
      | p => guardm (λa => if p a then pure a else failure)
  end

  section
    variable
      [Functor mn]

    def map : (α → β) → ⟦ Parser mn ρ α ⟶ Parser mn ρ β ⟧
      | f, _, ⟨p⟩ => ⟨λ mltn => Functor.map (Success.map f) ∘ p mltn⟩
    infixr:100 " <$> " => map

    def mapc : β → ⟦ Parser mn ρ α ⟶ Parser mn ρ β ⟧
      | b, _, p => const _ b <$> p
    infixr:100 " <$ " => mapc
  end

  section
    variable
      [Alternative mn]

    def failure [Alternative mn] : ⟦ Parser mn ρ α ⟧ := ⟨λ _ _ => Alternative.failure⟩

    def or [Functor mn] [Alternative mn] : ⟦ Parser mn ρ α ⟶ Parser mn ρ α ⟶ Parser mn ρ α ⟧
      | _, ⟨p⟩, ⟨q⟩ => Parser.mk λ mltn ts => p mltn ts <|> q mltn ts
    infixl:20 " <|> " => or
  end

  section
    variable
      [Monad mn]

    def andbind : ⟦ Parser mn ρ α ⟶ (const _ α ⟶ □ Parser mn ρ β) ⟶ Parser mn ρ (α × β) ⟧
      | _, pa, f => Parser.mk λ mlen ts => do
        let ra ← pa.run mlen ts
        let rb ← f ra.value |>.call (Nat.le_trans ra.small mlen) |>.run Nat.le.refl ra.leftovers
        pure (.and ra rb)
    infixl:55  " &>>= " => andbind

    def bind : ⟦ Parser mn ρ α ⟶ (const _ α ⟶ □ Parser mn ρ β) ⟶ Parser mn ρ β ⟧
      | _, pa, f => Prod.snd <$> (pa &>>= f)
    infixl:55  " >>= " => bind

    def and : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ β ⟶ Parser mn ρ (α × β) ⟧
      | _, a,  b => a &>>= const _ b
    infixl:60 " <&> " => and

    def left : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ β ⟶ Parser mn ρ α ⟧
      | _, a,  b => Prod.fst <$> (a <&> b)
    infixl:60 " <& " => left

    def right : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ β ⟶ Parser mn ρ β ⟧
      | _, a,  b => Prod.snd <$> (a <&> b)
    infixl:60 " &> " => right

    def amap : ⟦ Parser mn ρ (α → β) ⟶ □ Parser mn ρ α ⟶ Parser mn ρ β ⟧
      | _, pf, pa => (λ (f, a) => f a) <$> (pf <&> pa)
    infixl:60 " <*> " => amap

    def between : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ γ ⟶ □ Parser mn ρ β ⟶ Parser mn ρ β ⟧
      | _, pa, pc, pb => pa &> pb <& pc

    variable
      [Alternative mn]

    def andmbind [Alternative mn]: ⟦ Parser mn ρ α ⟶ (const _ α ⟶ □ Parser mn ρ β) ⟶ Parser mn ρ (α × Option β) ⟧
      | _, pa, f => Parser.mk λ mlen ts => do
        let ra ← pa.run mlen ts
        let slen := Nat.le_trans ra.small mlen
        let rb := f ra.value |>.call slen |>.run Nat.le.refl ra.leftovers
        Functor.map (λx => Success.and ra <| x.map pure) rb  <|> pure (ra.map (λ a => (a, none)))
    infixl:55  " &?>>= " => andmbind

    def ando : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ β ⟶ Parser mn ρ (α × Option β) ⟧
      | _, a,  b => a &?>>= const _ b
    infixl:60 " <&?> " => ando

    def lefto : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ β ⟶ Parser mn ρ α ⟧
      | _, a,  b => Prod.fst <$> (a <&?> b)
    infixl:60 " <&? " => lefto

    def righto : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ β ⟶ Parser mn ρ (Option β) ⟧
      | _, a,  b => Prod.snd <$> (a <&?> b)
    infixl:60 " &?> " => righto

    def oand : ⟦ Parser mn ρ α ⟶ Parser mn ρ β ⟶ Parser mn ρ (Option α × β) ⟧
      | _, a,  b => (some <$> a) <&> b <|> (none, ·) <$> b
    infixl:60 " <?&> " => oand

    def oleft : ⟦ Parser mn ρ α ⟶ Parser mn ρ β ⟶ Parser mn ρ (Option α) ⟧
      | _, a,  b => Prod.fst <$> (a <?&> b)
    infixl:60 " <?& " => oleft

    def oright : ⟦ Parser mn ρ α ⟶ Parser mn ρ β ⟶ Parser mn ρ β ⟧
      | _, a,  b => Prod.snd <$> (a <?&> b)
    infixl:60 " ?&> " => oright
  end

  section List
    def alts [Alternative mn] : ⟦ List ∘ Parser mn ρ α ⟶ Parser mn ρ α ⟧ :=
      List.foldl or failure

    def ands [Monad mn] : ⟦ FreeSemigroup ∘ Parser mn ρ α ⟶ (Parser mn ρ $ FreeSemigroup α) ⟧ :=
      FreeSemigroup.foldr1 (λ p ps => map (uncurry FreeSemigroup.append) (and p ps))
      ∘ FreeSemigroup.map (map FreeSemigroup.of)
  end List

  section Tok
    variable
      [Monad mn] [Alternative mn]
      [Inspect ρ.Toks ρ.Tok]

    -- How to rewrite without tactic?
    -- TODO: Rewrite to support any token
    def anyTok : ⟦ Parser mn ρ ρ.Tok ⟧ := Parser.mk λ _ ts =>
      @Success.getTok ρ.Toks ρ.Tok _ _ ts |>.elim Alternative.failure $ λ t =>
        ρ.recordToken t.value *> pure t

    variable
      [DecidableEq ρ.Tok]

    def anyOf : List ρ.Tok → ⟦ Parser mn ρ ρ.Tok ⟧
      | ts => guard (λ c => ts ≠ [] ∧ ts.any (· = c)) anyTok

    def exact : ρ.Tok → ⟦ Parser mn ρ ρ.Tok ⟧ :=
      anyOf ∘ pure

    def exacts : FreeSemigroup ρ.Tok → ⟦ Parser mn ρ (FreeSemigroup ρ.Tok) ⟧ := λ ts =>
      -- ands (FreeSemigroup.map (λ t => @exact _ _ _ _ _ _ t _) ts)
      ands (FreeSemigroup.map (by exact exact ·) ts)
  end Tok

  section ChainsAndIteration
    variable
      [Monad mn] [Alternative mn]

    def schainl : ⟦ Success ρ.Toks α ⟶ □ (Parser mn ρ (α → α)) ⟶ mn ∘ Success (ρ.Toks) α ⟧ :=
      Box.fix $ λ rec sa op => rest rec sa op |> flip Alternative.orElse λ _ => pure sa
    where
      rest : ⟦ □ (Success ρ.Toks α ⟶ □ Parser mn ρ (α → α) ⟶ mn ∘ Success ρ.Toks α) ⟶ (Success ρ.Toks α ⟶ □ Parser mn ρ (α → α) ⟶ mn ∘ Success ρ.Toks α) ⟧ :=
      λ rec s op => do
        let sop ← op.call s.small |>.run Nat.le.refl s.leftovers
        let s' ← rec.call s.small (Success.map (· $ s.value) sop) (Box.Transitions.lt_lower s.small op)
        pure $ Success.lt_lift s.small s'

    def iteratel : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ (α → α) ⟶ Parser mn ρ α ⟧
      | _, a, op => Parser.mk λ mltn ts => do
        let sa ← a.run mltn ts
        schainl sa $ Box.Transitions.le_lower mltn op

    def hchainl : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ (α → β → α) ⟶ □ Parser mn ρ β ⟶ Parser mn ρ α ⟧
      | _, a, op, b => iteratel a $ Box.map2 amap (Box.map (map flip) op) (Box.duplicate b)

    def chainl1 : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ (α → α → α) ⟶ Parser mn ρ α ⟧
      | _, a, op => hchainl a op a

    def iterater : ⟦ Parser mn ρ (α → α) ⟶ Parser mn ρ α ⟶ Parser mn ρ α ⟧ :=
      Box.fix $ λ rec op a => rest rec op a <|> a
    where
      rest : ⟦ □ (Parser mn ρ (α → α) ⟶ Parser mn ρ α ⟶ Parser mn ρ α) ⟶ (Parser mn ρ (α → α) ⟶ Parser mn ρ α ⟶ Parser mn ρ α) ⟧ :=
        λ rec op a => Parser.mk $ λ mlen ts => do
          let sop ← op.run mlen ts
          let sopltn := Nat.le_trans sop.small mlen
          let op' := Transitions.lt_lower sopltn op
          let a' := Transitions.lt_lower sopltn a
          let r ← (rec.call sopltn op' a').run Nat.le.refl sop.leftovers
          pure $ Success.lt_lift sop.small $ r.map sop.value

    def hchainr : ⟦ Parser mn ρ α ⟶ □ (Parser mn ρ (α -> β -> β)) ⟶ Parser mn ρ β ⟶ Parser mn ρ β ⟧ :=
      λ a op b => flip iterater b $ flip amap op $ map (λ a f => f a) a

    def chainr1 : ⟦ Parser mn ρ α ⟶ □ Parser mn ρ (α → α → α) ⟶ Parser mn ρ α ⟧ :=
      λ p op => hchainr p op p
  end ChainsAndIteration

  section List
    variable
      [Monad mn] [Alternative mn]

    def list1 : ⟦ Parser mn ρ α ⟶ Parser mn ρ (FreeSemigroup α) ⟧ :=
    Box.fix $ λ rec pa =>
      map (λ (hd, tl) => ⟨hd, tl.elim [] FreeSemigroup.toList⟩)
      (ando pa (Box.app rec pa))
  end List
end Combinators

section
  variable
    {ρ : Parser.Parameters mn}
    [Monad mn] [Alternative mn]
    [Inspect ρ.Toks ρ.Tok]
    [Coe Char ρ.Tok] -- XXX: or should this be subtype?
    [DecidableEq ρ.Tok]

  namespace Chars

    def char : Char → ⟦ Parser mn ρ ρ.Tok ⟧ :=
      exact ∘ Coe.coe

    def string (t : {s : String // (s.data.length > 0)}) : ⟦ Parser mn ρ String ⟧ :=
      λ {n : ℕ} =>
      match t with
      | ⟨⟨[]⟩, h⟩ => by contradiction
      | ⟨⟨(x :: xs)⟩, _⟩ => by
        let s : FreeSemigroup Char := ⟨x, xs⟩
        let ss : FreeSemigroup  (Parser mn ρ ρ.Tok n) :=
          FreeSemigroup.map' (@char _ _ _ _ _ _ _ · n) s
        let ss' : Parser mn ρ (FreeSemigroup ρ.Tok) n := ands ss
        refine (mapc ?_ ss')
        exact t.val

    def space : ⟦ Parser mn ρ ρ.Tok ⟧ :=
      anyOf (Coe.coe <$> (" \t\n\r\x0c").data)

    def spaces : ⟦Parser mn ρ (FreeSemigroup ρ.Tok)⟧ :=
      list1 space

    def parens : ⟦□ (Parser mn ρ α) ⟶ Parser mn ρ α⟧ :=
      between (char '(') (box $ char ')')

    -- TODO: Rewrite remaining combinators
  end Chars

  namespace Numbers
    def decimalDigit : ⟦Parser mn ρ Nat⟧ := alts [
      0 <$ exact '0',
      1 <$ exact '1',
      2 <$ exact '2',
      3 <$ exact '3',
      4 <$ exact '4',
      5 <$ exact '5',
      6 <$ exact '6',
      7 <$ exact '7',
      8 <$ exact '8',
      9 <$ exact '9',
    ]

    def decimalNat : ⟦ Parser mn ρ Nat ⟧ :=
      FreeSemigroup.foldl (λ n d => 10 * n + d) 0 <$> list1 decimalDigit
  end Numbers
end
