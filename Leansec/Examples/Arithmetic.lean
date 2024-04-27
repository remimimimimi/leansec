import Leansec.Combinators
import Leansec.Running

namespace Leansec.Examples.Arithmetic
open Induction Combinators Combinators.Chars Combinators.Numbers

mutual
  inductive Expr where
    | Emb : Term → Expr
    | Add : Expr → Term → Expr
    | Sub : Expr → Term → Expr
  deriving Repr
 inductive Term where
    | Emb : Factor → Term
    | Mul : Term → Factor → Term
    | Div : Term → Factor → Term
  deriving Repr
 inductive Factor where
    | Emb : Expr → Factor
    | Lit : Nat → Factor
  deriving Repr
end

section Parser
  structure Language (mn : Type → Type) (ρ : Parser.Parameters mn) (n : ℕ) where
    expr : Parser mn ρ Expr n
    term : Parser mn ρ Term n
    factor : Parser mn ρ Factor n

  variable
    {ρ : Parser.Parameters mn}
    [Monad mn] [Alternative mn]
    [Inspect ρ.Toks ρ.Tok]
    [Coe Char ρ.Tok] -- XXX: or should this be subtype?
    [DecidableEq ρ.Tok]

  def language : ⟦ Language mn ρ ⟧ :=
    Box.fix $ λ rec =>
      let addop :=  or (Expr.Add <$ (exact '+'))
                       (Expr.Sub <$ (exact '-'))
      let mulop :=  or (Term.Mul <$ (exact '*'))
                       (Term.Div <$ (exact '/'))
      let factor := Combinators.or (Factor.Emb <$> (parens (Box.map Language.expr rec)))
                                   (Factor.Lit <$> decimalNat)
      let term := hchainl (Term.Emb <$> factor) (box mulop) (box factor)
      let expr := hchainl (Expr.Emb <$> term) (box addop) (box term)
      Language.mk expr term factor


  def language' := by
    refine @language Option ⟨Char, Vector Char, λ _ => some ()⟩ _ _ _ ?_ _
    simp
    refine ⟨?_⟩
    exact id

  example : runParserOption "(1235+1)" (Language.expr language') = some
    (Expr.Emb (Term.Emb (Factor.Emb
      (Expr.Add
        (Expr.Emb (Term.Emb (Factor.Lit 1235)))
        (Term.Emb (Factor.Lit 1)))))) := rfl
  example : runParserOption "1+(2*31-4)" (Language.expr language') = some
    (Expr.Add
      (Expr.Emb (Term.Emb
        (Factor.Lit 1)))
      (Term.Emb (Factor.Emb
        (Expr.Sub
          (Expr.Emb (Term.Mul
              (Term.Emb (Factor.Lit 2))
              (Factor.Lit 31)))
          (Term.Emb (Factor.Lit 4)))))) := rfl
end Parser
