import Aesop
import Leansec.Combinators

namespace Leansec

inductive Singleton : α → Type where
  | mk (v : α) : Singleton v

-- TODO: Adjust priority
postfix:max " !" => Singleton.mk

class Tokenizer (tok : Type) where
  tokenize : String → List tok
  lessTokens : (s : String) → (tokenize s).length ≤ s.length

instance : Tokenizer Char where
  tokenize := String.data
  lessTokens s := by constructor

class SizedInput (tok : Type) (toks : Nat → Type) where
  sizedInput : (ts : List tok) → toks ts.length

instance : SizedInput α (Vector α) where
  sizedInput ts := ts.toArray.toVector

class MonadRun (m : Type → Type) where
  runMonad : m a → List a

instance : MonadRun List where
  runMonad := id

instance : MonadRun Option where
  runMonad := Option.toList

def runParserOption {ρ : Parser.Parameters _} [MonadRun mn] [Tokenizer ρ.Tok] [SizedInput ρ.Tok ρ.Toks]
  (str : String) (p : ⟦ Parser mn ρ α ⟧) : Option α :=
  let input := Tokenizer.tokenize (tok := ρ.Tok) str |> SizedInput.sizedInput (tok := ρ.Tok) (toks := ρ.Toks)
  let result := p.run (Tokenizer.lessTokens str) input
  MonadRun.runMonad result |>.filterMap Success.complete |>.head?

-- def runParserOption (input : String) (p : Parser Option ⟨Char, Vector Char, λ _ => some ()⟩ α input.length) : Option α :=
--   @Parser.run Option
--     _
--     _
--     input.length
--     p
--     input.length
--     Nat.le.refl
--     ⟨input.toList.toArray, rfl⟩
--   |>.map Success.complete
--   |>.join

def runParserType {ρ : Parser.Parameters _} [MonadRun mn] [Tokenizer ρ.Tok] [SizedInput ρ.Tok ρ.Toks]
  (str : String) (p : ⟦ Parser mn ρ α ⟧) : Type :=
  runParserOption str p |>.elim Empty Singleton

infix:50 " ∈ " => runParserType
