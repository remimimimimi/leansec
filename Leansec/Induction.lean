import Leansec.Indexed

namespace Leansec.Induction

structure Box (α : Nat → Type u) (n : Nat) : Type u where
  call : ∀{m}, m < n → α m
prefix:40 "□ " => Box

namespace Box
def map (f : ⟦ α ⟶ β ⟧) : ⟦ □ α ⟶ □ β ⟧ :=
  λ ⟨a⟩ => ⟨f ∘ a⟩

def map2 (f : ⟦ α ⟶ β ⟶ γ ⟧) : ⟦ □ α ⟶ □ β ⟶ □ γ ⟧ :=
  λ ⟨a⟩ ⟨b⟩ => ⟨λ mltn => f (a mltn) (b mltn)⟩

def extract : ⟦ □ α ⟧ → ⟦ α ⟧ :=
  λ ⟨a⟩ => a Nat.le.refl

def duplicate : ⟦ □ α ⟶ □ □ α ⟧ :=
  λ ⟨a⟩ => ⟨λ mltn => ⟨λ pltm => a (Nat.lt_trans pltm mltn)⟩⟩

def app : ⟦ □ (α ⟶ β) ⟶ □ α ⟶ □ β⟧ :=
  λ ⟨f⟩ ⟨a⟩ => ⟨λ mltn => f mltn (a mltn)⟩

def fixb : ⟦ □ α ⟶ α ⟧ → ⟦ □ α ⟧ := fixBox
where
  fixBox
  | _, 0 => ⟨λ {m} mlt0 => absurd mlt0 (Nat.not_lt_zero m)⟩
  | f, n + 1 =>
    ⟨λ mltsn => f ⟨λ pltm =>
      (fixBox f n).call (Nat.le_trans pltm (Nat.le_of_lt_succ mltsn))⟩⟩

def fix : ⟦ □ α ⟶ α ⟧ → ⟦ α ⟧ := extract ∘ fixb

def loeb : ⟦ □ (□ α ⟶ α) ⟶ □ α ⟧ :=
  fix (λ rec alg => app alg (app rec (duplicate alg)))

namespace Transitions
  def le_close (down : ∀ m n, m ≤ n → α n → α m) : ⟦ α ⟶ □ α ⟧ :=
    λ a => ⟨λ mltn => down _ _ (Nat.le_of_lt mltn) a⟩

  def le_lower (mlen : m ≤ n) (b : (□ α) n) : (□ α) m :=
    ⟨λ pltm => b.call (Nat.le_trans pltm mlen)⟩

  def lt_lower (mlen : m < n) (b : (□ α) n) : (□ α) m :=
    ⟨λ pltm => b.call (Nat.lt_trans pltm mlen)⟩
