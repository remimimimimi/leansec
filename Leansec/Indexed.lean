namespace Leansec.Indexed

variable
  {ι : Type u}
  (α : ι → Type u)
  (β : ι → Type u)
  (i : ι)

abbrev arrow := α i → β i
abbrev product := α i × β i
abbrev const (α : Type u) (_ : ι) := α
abbrev bind := ∀{n}, α n

-- Regular arrow have precedence 25
infixr:29 " ⟶ " => arrow
infixr:35 " ⊗ " => product
prefix:38 "κ " => const
notation:27 "⟦ " α " ⟧" => bind α
