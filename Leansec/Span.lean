namespace Leansec.Span

structure Position : Type where
  line : Nat
  column : Nat
deriving Inhabited, DecidableEq

def update (x : Char) (ρ : Position) : Position :=
  if x == '\n'
    then {ρ with line := ρ.line + 1, column := 0}
    else {ρ with column := ρ.column + 1}

def updates (s : String) (ρ : Position) : Position :=
  s.foldl (flip update) ρ

instance : Repr Position where
  reprPrec p _ := Std.Format.text <| s!"{p.line}:{p.column}"
