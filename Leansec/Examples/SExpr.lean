import Leansec.Combinators
import Leansec.Lexer
import Leansec.Running

namespace Leansec.Examples.SExpr
open Induction Combinators Combinators.Chars Combinators.Numbers Lexer Span

inductive Token
| LPar
| RPar
| Id : String → Token
deriving Repr, DecidableEq

instance : Coe Char Token where
  coe
    | '(' => .LPar
    | ')' => .RPar
    | _ => .Id ""               -- Should be unreachable

def toks : List (String × Token) := []

def breaking (c : Char) : MaybeBreaking Token :=
  if c.isWhitespace then .breaking none else parens c
where
  parens : Char → MaybeBreaking Token
  | '(' => .breaking $ some .LPar
  | ')' => .breaking $ some .RPar
  | _ => .not_breaking

abbrev TokenizerParams : LexParameters where
  Tok := Token
  keywords := toks
  breaking := breaking
  default := .Id

instance : Tokenizer (Position × TokenizerParams.Tok) where
  tokenize := @tokenize TokenizerParams
  lessTokens := lessTokens

inductive SExp where
| Atom : String → SExp
| List : List SExp → SExp

def inp : String := "( hello world )"

-- #eval @tokenize TokenizerParams inp

variable
  [Monad mn]
  [Alternative mn]
  [DecidableEq Token]

abbrev Params : Parser.Parameters mn where
  Tok := Token
  Toks := Vector Token
  recordToken := λ _ => pure ()

-- variable
--    [Inspect Params.Toks Params.Tok]
--    [Coe Char Params.Tok]

def id : ⟦ Parser Option Params String ⟧ := guardm (λ t =>
  match t with
  | .Id s => some s
  | _ => none
) anyTok

-- def sexp_list : ⟦ □ Parser Option Params Sexp ⟶ Parser Option Params (List SExp) ⟧ := λ r =>
--   Combinators.map _ $ parens $ headAndTail (Combinators.map id)

#check (⟨1, [2, 3]⟩ : FreeSemigroup _)

-- def sexpr : ⟦ Parser Option Params SExp ⟧ := Box.fix $ λ r =>
--     alts [
--       Combinators.map SExp.Atom id,
--       -- Combinators.mapc (SExp.List []) (Combinators.exacts (⟨Token.LPar, [Token.RPar]⟩ : FreeSemigroup _)),
--       Combinators.map SExp.List $ parens _
--       -- parens $ alts [
--       --   Combinators.map (λ t => by {

--       --   }) $ list1 r
--       -- ]
--     ]



-- section Parser
--   structure Language (mn : Type → Type) (ρ : Parser.Parameters mn) (n : ℕ) where
--     expr : Parser mn ρ Expr n
--     term : Parser mn ρ Term n
--     factor : Parser mn ρ Factor n

--   variable
--     {ρ : Parser.Parameters mn}
--     [Monad mn] [Alternative mn]
--     [Inspect ρ.Toks ρ.Tok]
--     [Coe Char ρ.Tok] -- XXX: or should this be subtype?
--     [DecidableEq ρ.Tok]

--   def language : ⟦ Language mn ρ ⟧ :=
--     Box.fix $ λ rec =>
--       let addop :=  or (Expr.Add <$ (exact '+'))
--                        (Expr.Sub <$ (exact '-'))
--       let mulop :=  or (Term.Mul <$ (exact '*'))
--                        (Term.Div <$ (exact '/'))
--       let factor := Combinators.or (Factor.Emb <$> (parens (Box.map Language.expr rec)))
--                                    (Factor.Lit <$> decimalNat)
--       let term := hchainl (Term.Emb <$> factor) (box mulop) (box factor)
--       let expr := hchainl (Expr.Emb <$> term) (box addop) (box term)
--       Language.mk expr term factor


--   def language' := by
--     refine @language Option ⟨Char, Vector Char, λ _ => some ()⟩ _ _ _ ?_ _
--     simp
--     refine ⟨?_⟩
--     exact id

--   example : "(1235+1)" ∈ language'.expr :=
--     (Expr.Emb (Term.Emb (Factor.Emb
--       (Expr.Add
--         (Expr.Emb (Term.Emb (Factor.Lit 1235)))
--         (Term.Emb (Factor.Lit 1)))))) !

--   example : "1+(2*31-4)" ∈ language'.expr :=
--     (Expr.Add
--       (Expr.Emb (Term.Emb
--         (Factor.Lit 1)))
--       (Term.Emb (Factor.Emb
--         (Expr.Sub
--           (Expr.Emb (Term.Mul
--               (Term.Emb (Factor.Lit 2))
--               (Factor.Lit 31)))
--           (Term.Emb (Factor.Lit 4)))))) !
-- end Parser
