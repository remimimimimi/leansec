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
  def le_lower : m ≤ n → Parser α n → Parser α m
    | mlen, ⟨p⟩ => ⟨λ plem => p (Nat.le_trans plem mlen)⟩

  def lt_lower : m < n → Parser α n → Parser α m
    | mltn => le_lower (Nat.le_of_lt mltn)
end Transitions

def box : ⟦Parser α ⟶ □ Parser α⟧ :=
  Box.Transitions.le_close (λ_ _ => Transitions.le_lower)

instance : Coe (Parser α n) ((□ Parser α) n) where
  coe := box

-- TODO: Implement combinators as instances of corresponding type classes to
-- avoid ambiguity in notation. Understand how to implement Functor and other
-- type classes for indexed types, because typechecker fails when flipping
-- happing.
--
-- If we could do it, then we can get rid of some of new notation declaration as
-- they're already defined in `Init` library.
section Combinators
  def guardM (f : α → Option β) : ⟦Parser α ⟶ Parser β⟧
    | _, ⟨p⟩ => ⟨λ mltn ts => p mltn ts >>= Success.guardM f⟩

  def guard : (α → Bool) → ⟦Parser α ⟶ Parser α⟧
    | p => guardM (λa => if p a then pure a else failure)

  def map : (α → β) → ⟦Parser α ⟶ Parser β⟧
    | f, _, ⟨p⟩ => ⟨λ mltn => Option.map (Success.map f) ∘ p mltn⟩
  infixr:100 " <$> " => map

  def mapc : β → ⟦Parser α ⟶ Parser β⟧
    | b, _, p => const _ b <$> p
  infixr:100 " <$ " => mapc

  def failure : ⟦Parser α⟧ := ⟨λ _ _ => Alternative.failure⟩

  def or : ⟦Parser α ⟶ Parser α ⟶ Parser α⟧
    | _, ⟨p⟩, ⟨q⟩ => Parser.mk λ mltn ts => p mltn ts |>.orElse (λ_ => q mltn ts)

  infixl:20 " <|> " => or

  def andmbind : ⟦Parser α ⟶ (const _ α ⟶ □ Parser β) ⟶ Parser (α × Option β)⟧
    | _, pa, f => Parser.mk λ mlen ts => do
      let ra ← pa.run mlen ts
      let slen := Nat.le_trans ra.small mlen
      let rb := f ra.value |>.call slen |>.run Nat.le.refl ra.leftovers
      pure $ match rb with
      | some rb' => Success.and ra (rb'.map some)
      | none => ra.map (λa => (a, none))
  infixl:55  " &?>>= " => andmbind

  def andbind : ⟦Parser α ⟶ (const _ α ⟶ □ Parser β) ⟶ Parser (α × β)⟧
    | _, pa, f => Parser.mk λ mlen ts => do
      let ra ← pa.run mlen ts
      let rb ← f ra.value |>.call (Nat.le_trans ra.small mlen) |>.run Nat.le.refl ra.leftovers
      pure (.and ra rb)
  infixl:55  " &>>= " => andbind

  def bind : ⟦Parser α ⟶ (const _ α ⟶ □ Parser β) ⟶ Parser β⟧
    | _, pa, f => Prod.snd <$> (pa &>>= f)
  infixl:55  " >>= " => bind

  def and : ⟦Parser α ⟶ □ Parser β ⟶ Parser (α × β)⟧
    | _, a,  b => a &>>= const _ b
  infixl:60 " <&> " => and

  def left : ⟦Parser α ⟶ □ Parser β ⟶ Parser α⟧
    | _, a,  b => Prod.fst <$> (a <&> b)
  infixl:60 " <& " => left

  def right : ⟦Parser α ⟶ □ Parser β ⟶ Parser β⟧
    | _, a,  b => Prod.snd <$> (a <&> b)
  infixl:60 " &> " => right

  def amap : ⟦Parser (α → β) ⟶ □ Parser α ⟶ Parser β⟧
    | _, pf, pa => (λ (f, a) => f a) <$> (pf <&> pa)
  infixl:60 " <*> " => amap

  def ando : ⟦Parser α ⟶ □ Parser β ⟶ Parser (α × Option β)⟧
    | _, a,  b => a &?>>= const _ b
  infixl:60 " <&?> " => ando

  def lefto : ⟦Parser α ⟶ □ Parser β ⟶ Parser α⟧
    | _, a,  b => Prod.fst <$> (a <&?> b)
  infixl:60 " <&? " => lefto

  def righto : ⟦Parser α ⟶ □ Parser β ⟶ Parser (Option β)⟧
    | _, a,  b => Prod.snd <$> (a <&?> b)
  infixl:60 " &?> " => righto

  def oand : ⟦Parser α ⟶ Parser β ⟶ Parser (Option α × β)⟧
    | _, a,  b => (some <$> a) <&> b <|> (none, ·) <$> b
  infixl:60 " <?&> " => oand

  def oleft : ⟦Parser α ⟶ Parser β ⟶ Parser (Option α)⟧
    | _, a,  b => Prod.fst <$> (a <?&> b)
  infixl:60 " <?& " => oleft

  def oright : ⟦Parser α ⟶ Parser β ⟶ Parser β⟧
    | _, a,  b => Prod.snd <$> (a <?&> b)
  infixl:60 " ?&> " => oright

  def between : ⟦Parser α ⟶ □ Parser γ ⟶ □ Parser β ⟶ Parser β⟧
    | _, pa, pc, pb => pa &> pb <& pc

  section List
    def alts : ⟦List ∘ Parser α ⟶ Parser α⟧ :=
      List.foldl or failure

    def ands : ⟦FreeSemigroup ∘ Parser α ⟶ (Parser $ FreeSemigroup α)⟧ :=
      FreeSemigroup.foldr1 (λ p ps => map (uncurry FreeSemigroup.append) (and p ps))
      ∘ FreeSemigroup.map (map FreeSemigroup.of)
  end List

  section Tok
    -- How to rewrite without tactic?
    -- TODO: Rewrite to support any token
    def anyTok : ⟦Parser Tok⟧ := ⟨λ _ => λ
      | ⟨[], _⟩ => none
      | ⟨t :: ts, h⟩ => pure (Success.mk' t (by simp [←h]) ⟨ts, rfl⟩)⟩

    def anyOf : List Tok → ⟦Parser Tok⟧
      | ts => guard (λ c => ts ≠ [] ∧ ts.any (· = c)) anyTok

    def exact : Tok → ⟦Parser Tok⟧ :=
      anyOf ∘ pure

    def exacts : FreeSemigroup Tok → ⟦Parser (FreeSemigroup Tok)⟧ := λ ts =>
      ands (FreeSemigroup.map (λ t => @exact t _) ts)
  end Tok

  section ChainsAndIteration
    def schainl : ⟦Success α ⟶ □ Parser (α → α) ⟶ Option ∘ Success α⟧ :=
      Box.fix $ λ rec sa op => rest rec sa op |>.orElse λ _ => pure sa
    where
      rest : ⟦□ (Success α ⟶ □ Parser (α → α) ⟶ Option ∘ Success α) ⟶ (Success α ⟶ □ Parser (α → α) ⟶ Option ∘ Success α)⟧ :=
      λ rec s op => do
        let sop ← op.call s.small |>.run Nat.le.refl s.leftovers
        let s' ← rec.call s.small (Success.map (· $ s.value) sop) (Box.Transitions.lt_lower s.small op)
        pure $ Success.lt_lift s.small s'

    def iterate : ⟦Parser α ⟶ □ Parser (α → α) ⟶ Parser α⟧
      | _, a, op => Parser.mk λ mltn ts => do
        let sa ← a.run mltn ts
        schainl sa $ Box.Transitions.le_lower mltn op

    def hchainl : ⟦Parser α ⟶ □ Parser (α → β → α) ⟶ □ Parser β ⟶ Parser α⟧
      | _, a, op, b => iterate a $ Box.map2 amap (Box.map (map flip) op) (Box.duplicate b)

    def chainl1 : ⟦Parser α ⟶ □ Parser (α → α → α) ⟶ Parser α⟧
      | _, a, op => hchainl a op a

    -- def chainr1 : ⟦Parser α ⟶ □ Parser (α → α → α) ⟶ Parser α⟧ :=
    --   Box.fix $ λ rec a op => Parser.mk λ mlen s => do
    --     let sa ← a.run mlen s
    --     _
    -- where
    --   rest : ⟦□ (Parser α ⟶ □ Parser (α → α → α) ⟶ Parser α) ⟶
    --              Parser α ⟶ □ Parser (α → α → α) ⟶ Success α ⟶ Option ∘ Success α⟧
    --     | _, rec, a, op, sa => do
    --       let sop ← op.call sa.small |>.run Nat.le.refl sa.leftovers
    --       let sop' := sop
    --       _
  end ChainsAndIteration

  section List
    def list1 : ⟦Parser α ⟶ Parser (FreeSemigroup α)⟧ :=
    Box.fix $ λ rec pa =>
      map (λ (hd, tl) => ⟨hd, tl.elim [] FreeSemigroup.toList⟩)
      (ando pa (Box.app rec pa))
  end List
end Combinators
