import Mathlib.Algebra.Free

namespace FreeSemigroup
  def toList (x : FreeSemigroup α) : List α := x.head :: x.tail

  def fromList : List α → Option (FreeSemigroup α)
    | [] => none
    | x :: xs => some (FreeSemigroup.mk x xs)

  def cons (hd : α) (xxs : FreeSemigroup α) : FreeSemigroup α := ⟨hd, xxs.toList⟩

  def map' (f : α → β) : FreeSemigroup α → FreeSemigroup β
    | ⟨x, xs⟩ => ⟨f x, xs.map f⟩

  def foldl (f : β → α → β) (init : β) (xxs : FreeSemigroup α) : β :=
    List.foldl f init $ toList xxs

  def foldr (f : α → β → β) (init : β) (xxs : FreeSemigroup α) : β :=
    List.foldr f init $ toList xxs

  def foldl1 (f : α → α → α) (xxs : FreeSemigroup α) : α :=
    List.foldl f xxs.head xxs.tail

  def foldr1 (f : α → α → α) (xxs : FreeSemigroup α) : α :=
    List.foldr f xxs.head xxs.tail

  def append : FreeSemigroup α → FreeSemigroup α → FreeSemigroup α :=
    flip $ foldr cons
end FreeSemigroup
