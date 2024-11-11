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

def mkeps (h : Σ' r : RegularExpression α, r.matchEpsilon) : (Σ' v : Value α, Inhab v h.fst) :=
  match h with
  | ⟨epsilon, _⟩ => ⟨Value.empty, Inhab.empty⟩
  | ⟨comp r₁ r₂, hn⟩ => by
    simp [matchEpsilon] at hn
    have h₁ := mkeps ⟨r₁, hn.left⟩
    have h₂ := mkeps ⟨r₂, hn.right⟩
    refine ⟨Value.seq h₁.fst h₂.fst, ?_⟩
    apply Inhab.seq
    exact h₁.snd
    exact h₂.snd
  | ⟨plus r₁ r₂, hn⟩ => by
    if hn₁ : r₁.matchEpsilon
      then
        have h₁ := mkeps ⟨r₁, hn₁⟩
        refine ⟨Value.left h₁.fst, ?_⟩
        apply Inhab.left
        exact h₁.snd
      else
        simp [matchEpsilon] at hn
        have h₂ := mkeps ⟨r₂, Or.resolve_left hn hn₁⟩
        refine ⟨Value.right h₂.fst, ?_⟩
        apply Inhab.right
        exact h₂.snd
  | ⟨star r, hn⟩ => ⟨Value.stars [], Inhab.star_nil r⟩
termination_by h.fst.size

variable [DecidableEq α]

def inj : (r : RegularExpression α) → (c : α) → (Σ' v : Value α, Inhab v (r.deriv c)) → (Σ' v : Value α, Inhab v r)
  | char d, c, ⟨v, h⟩ => by
    simp [deriv] at h
    split_ifs at h
    · match v with
      | Value.empty => exact  ⟨Value.char d, Inhab.char d⟩
    · rw [←RegularExpression.zero_def] at h
      simp only [inhab_zero] at h
  | plus r₁ r₂, c, PSigma.mk (Value.left v₁) h => by
    simp at h
    apply inhab_left at h
    have h₁ := inj r₁ c ⟨v₁, h⟩
    refine ⟨Value.left h₁.fst, ?_⟩
    apply Inhab.left
    exact h₁.snd
  | plus r₁ r₂, c, PSigma.mk (Value.right v₂) h => by
    simp at h
    apply inhab_right at h
    have h₂ := inj r₂ c ⟨v₂, h⟩
    refine ⟨Value.right h₂.fst, ?_⟩
    apply Inhab.right
    exact h₂.snd
  | comp r₁ r₂, c, ⟨v, h⟩ => by
    simp [deriv] at h
    split_ifs at h with hr₁
    · match v with
      | Value.left v₁ =>
        apply inhab_left at h
        match v₁ with
        | Value.seq v₁ v₂ =>
          apply inhab_seq at h
          have h₁ := inj r₁ c ⟨v₁, h.left⟩
          refine ⟨Value.seq h₁.fst v₂, ?_⟩
          apply Inhab.seq
          exact h₁.snd
          exact h.right
      | Value.right v₂ =>
        apply inhab_right at h
        have h₁ := mkeps ⟨r₁, hr₁⟩
        have h₂ := inj r₂ c ⟨v₂, h⟩
        refine ⟨Value.seq h₁.fst h₂.fst, ?_⟩
        apply Inhab.seq
        exact h₁.snd
        exact h₂.snd
    · match v with
      | Value.seq v₁ v₂ =>
        apply inhab_seq at h
        have h₁ := inj r₁ c ⟨v₁, h.left⟩
        refine ⟨Value.seq h₁.fst v₂, ?_⟩
        apply Inhab.seq
        exact h₁.snd
        exact h.right
  | star r, c, PSigma.mk (Value.seq v (Value.stars vs)) h => by
    simp [deriv] at h
    apply inhab_seq at h
    have h₁ := inj r c ⟨v, h.left⟩
    refine ⟨Value.stars (h₁.fst :: vs), ?_⟩
    apply Inhab.stars
    exact h₁.snd
    exact h.right

def lexer (r : RegularExpression α) (s : List α) : Option (Σ' v : Value α, Inhab v r) :=
  match s with
  | [] => if hr : r.matchEpsilon then some (mkeps ⟨r, hr⟩) else none
  | x::xs =>
    match lexer (r.deriv x) xs with
    | none => none
    | some v => some (inj r x v)

def lexer' (r : RegularExpression α) (s : List α) : Option (Value α) :=
  match lexer r s with
  | none => none
  | some v => some v.fst
