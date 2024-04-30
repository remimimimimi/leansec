import Leansec.Combinators

namespace Leansec

def runParserOption (input : String) (p : Parser Option ⟨Char, Vector Char, λ _ => some ()⟩ α input.length) : Option α :=
  @Parser.run Option
    _
    _
    input.length
    p
    input.length
    Nat.le.refl
    ⟨input.toList, rfl⟩
  |>.map Success.complete
  |>.join

inductive Singleton : α → Type where
  | mk (v : α) : Singleton v

-- TODO: Adjust priority
postfix:max " !" => Singleton.mk

def runParserType (input : String) (p : Parser Option ⟨Char, Vector Char, λ _ => some ()⟩ α input.length) : Type :=
  runParserOption input p |>.elim Empty Singleton

infix:50 " ∈ " => runParserType
