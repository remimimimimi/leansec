namespace Leansec.Span

-- TODO: before TParserT
-- -- class Position (α c : Type u) where
-- --   offset : α → Nat
-- --   line : α → Nat
-- --   column : α → Nat

-- --   isSeparator : c → Bool

-- structure Position (p : c → Bool) : Type where
--   offset : Nat
--   line : Nat
--   column : Nat
-- deriving Repr, Inhabited, DecidableEq

-- -- #check List.foldl

-- def update {p : c → Bool} (x : c) (ρ : Position p) : Position p :=
--   let ρ' : Position p := {ρ with offset := ρ.offset + 1}
--   if p x
--     then {ρ' with line := ρ'.line + 1, column := 0}
--     else {ρ' with column := ρ'.column + 1}

-- -- NOTE: I stopped here

-- -- structure Span (α : Type u) where
-- --   pos : Position p
-- --   value : α

-- -- instance [Position α] : Repr α where
-- --   reprPrec s := Repr.reprPrec (s!"{Position.line s}:{Position.column s}")
