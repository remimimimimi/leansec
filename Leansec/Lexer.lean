import Aesop
import Lean.Data.Trie
import Leansec.Span
import Mathlib.Logic.Function.Defs

namespace Leansec.Lexer

open Lean.Data
open Leansec.Span

inductive MaybeBreaking (tok : Type) where
  | breaking : Option tok → MaybeBreaking tok
  | not_breaking : MaybeBreaking tok

structure LexParameters where
  -- Our lexer is parametrised over the type of tokens
  Tok : Type
  -- We start with an association list between
  -- * keywords (as Strings)
  -- * keywords (as token values)
  keywords : List (String × Tok)
  -- We also need to be able to determine which characters are breaking.
  breaking : Char → MaybeBreaking Tok
  -- Finally, strings which are not decoded as keywords are coerced using a
  -- function to token values.
  default : String → Tok

abbrev LexResult (p : LexParameters) : Type := List (Position × p.Tok)
abbrev Keywords (p : LexParameters) : Type := Trie p.Tok

def tokenize.internal {p : LexParameters} (kw : Keywords p) (s : List Char) (pos : Position) (start? : Option Position) (buf : String) (acc : LexResult p) : LexResult p :=
  match s with
  | [] =>
    let acc := if buf.isEmpty then acc else
      let tok := match kw.find? buf with
                 | some k => k
                 | none   => p.default buf
      (start?.getD pos, tok) :: acc
    acc.reverse
  | c :: cs =>
    let pos' := update c pos
    match p.breaking c with
    | .breaking none =>
      let acc :=
        if buf.isEmpty then acc else
          let tok := match kw.find? buf with
                     | some k => k
                     | none => p.default buf
          (start?.getD pos, tok) :: acc
      tokenize.internal kw cs pos' none "" acc
    | .breaking (some t) =>
      let acc :=
        if buf.isEmpty then acc else
          let tok := match kw.find? buf with
                     | some k => k
                     | none => p.default buf
          (start?.getD pos, tok) :: acc
      let acc := (pos, t) :: acc
      tokenize.internal kw cs pos' none "" acc
    | .not_breaking =>
      let start? := start?.or $ some pos
      tokenize.internal kw cs pos' start? (buf.push c) acc

def tokenize {p : LexParameters} (s : String) : LexResult p :=
  let kw : Keywords p :=
    p.keywords.foldl (λ p ⟨ s, t ⟩ => p.insert s t) Inhabited.default
  tokenize.internal kw s.toList default none "" []

-- TODO: Prove
axiom lessTokens {p : LexParameters} (s : String) : (@tokenize p s).length ≤ s.length -- := by
--   unfold tokz
--   simp [String.length]
--   induction s.data with
--   | nil => simp [tokenize.internal]; constructor
--   | cons c cs h =>
--     simp
--     generalize kw_def : (List.foldl (fun p_1 x ↦ Trie.insert p_1 x.fst x.snd) default p.keywords) = kw at *
--     unfold tokenize.internal
--     match p.breaking c with
--     | .breaking none => sorry
--     | .breaking (some t) => sorry
--     | .not_breaking =>
--       simp
--       -- apply?
--       refine Nat.le_add_right_of_le ?_

--       sorry


-- def myParams : LexParameters where
--   Tok      := String
--   keywords := [("+", "+"), ("-", "-"), ("if", "if"), ("then", "then")]
--   breaking := λ c =>
--     if c.isWhitespace then MaybeBreaking.breaking none
--     else if c == '+' then MaybeBreaking.breaking (some "+")
--     else if c == '-' then MaybeBreaking.breaking (some "-")
--     else MaybeBreaking.not_breaking
--   default  := id  -- leave identifiers/numbers as raw strings

-- #eval @tokenize myParams "if x+ y -42 then"
-- #eval @tokz myParams "if x+ y -42 then"
