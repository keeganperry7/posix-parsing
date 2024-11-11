import Mathlib.Computability.RegularExpressions
import RegexPosix.Value

universe u

variable {α : Type u}

open RegularExpression

@[simp]
def RegularExpression.size : RegularExpression α → Nat
  | zero => 1
  | epsilon => 1
  | char _ => 1
  | plus r₁ r₂ => 1 + r₁.size + r₂.size
  | comp r₁ r₂ => 1 + r₁.size + r₂.size
  | star r => 1 + r.size

def mkeps (h : Σ' r : RegularExpression α, r.matchEpsilon) : Value α :=
  match h with
  | ⟨epsilon, _⟩ => Value.empty
  | ⟨comp r₁ r₂, hn⟩ => by
    simp [matchEpsilon] at hn
    exact Value.seq (mkeps ⟨r₁, hn.left⟩) (mkeps ⟨r₂, hn.right⟩)
  | ⟨plus r₁ r₂, hn⟩ =>
    if hn₁ : r₁.matchEpsilon
      then Value.left (mkeps ⟨r₁, hn₁⟩)
      else by
        simp [matchEpsilon] at hn
        exact Value.right (mkeps ⟨r₂, Or.resolve_left hn hn₁⟩)
  | ⟨star r, hn⟩ => Value.stars []
termination_by h.fst.size
