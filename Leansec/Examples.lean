import Leansec.Combinators
import Leansec.Running

namespace Leansec.Examples
namespace Arithmetic
open Induction Combinators

section Ast
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
end Ast

section Parser
  structure Language (n : Nat) where
    expr : Parser Expr n
    term : Parser Term n
    factor : Parser Factor n

  def parens : ⟦□ Parser α ⟶ Parser α⟧ :=
    between (exact '(') (box (exact ')'))

  def decimal_digit : ⟦Parser Nat⟧ := alts [
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

  def decimal_nat : ⟦ Parser Nat ⟧ :=
    map (FreeSemigroup.foldl (λ n d => 10 * n + d) 0)
        (list1 decimal_digit)

  def language : ⟦ Language ⟧ :=
    Box.fix $ λ rec =>
      let addop :=  or (Expr.Add <$ (exact '+'))
                       (Expr.Sub <$ (exact '-'))
      let mulop :=  or (Term.Mul <$ (exact '*'))
                       (Term.Div <$ (exact '/'))
      let factor := Combinators.or (Factor.Emb <$> (parens (Box.map Language.expr rec)))
                                   (Factor.Lit <$> decimal_nat)
      let term := hchainl (Term.Emb <$> factor) (box mulop) (box factor)
      let expr := hchainl (Expr.Emb <$> term) (box addop) (box term)
      Language.mk expr term factor

  example : runParser "(1235+1)" language.expr = some
    (Expr.Emb (Term.Emb (Factor.Emb
      (Expr.Add
        (Expr.Emb (Term.Emb (Factor.Lit 1235)))
        (Term.Emb (Factor.Lit 1)))))) := rfl
  example : runParser "1+(2*31-4)" language.expr = some
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
end Arithmetic
