import Leansec.Combinators

namespace Leansec

-- TODO:
-- def check : String → ⟦Parser α⟧


def runParser (input : String) (p : Parser α (input.length)) :=
  @Parser.run _ input.length p input.length (Nat.le.refl) ⟨input.toList, rfl⟩ |>.map Success.value
