import Leansec.Combinators

namespace Leansec

-- TODO:
-- def check : String → ⟦Parser α⟧


def runParserOption (input : String) (p : Parser Option ⟨Char, Vector Char, λ _ => some ()⟩ α (input.length)) :=
  @Parser.run Option
    _
    _
    input.length
    p
    input.length
    Nat.le.refl
    ⟨input.toList, rfl⟩
  |>.map Success.value
