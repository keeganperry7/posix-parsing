import RegexPosix.Value

open Parse
open Regex

universe u

variable {α : Type u}

inductive POSIX : {r : Regex α} → Parse r → Prop
  | epsilon : POSIX empty
  | char (c : α) : POSIX (char c)
  | left {r₁ : Regex α} {p : Parse r₁} :
    POSIX p →
    POSIX p.left
  | right {r₁ r₂ : Regex α} {p : Parse r₂} :
    POSIX p →
    ¬r₁.Matches p.flat →
    POSIX (r := r₁.plus r₂) p.right
  | mul {r₁ r₂ : Regex α} {p₁ : Parse r₁} {p₂ : Parse r₂} :
    POSIX p₁ →
    POSIX p₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = p₂.flat ∧ r₁.Matches (p₁.flat ++ s₃) ∧ r₂.Matches s₄) →
    POSIX (p₁.seq p₂)
  | star_nil :
    POSIX star_nil
  | star_cons {r : Regex α} {p : Parse r} {ps : Parse (star r)} :
    POSIX p →
    POSIX ps →
    p.flat ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = ps.flat ∧ r.Matches (p.flat ++ s₃) ∧ (star r).Matches s₄) →
    POSIX (p.star_cons ps)

theorem POSIX.matches {r : Regex α} {p : Parse r} : POSIX p → r.Matches p.flat :=
  fun _ => p.matches

theorem longest_split_unique {r₁ r₂ : Regex α} {s₁₁ s₁₂ s₂₁ s₂₂ : List α}
  (hs : s₁₁ ++ s₁₂ = s₂₁ ++ s₂₂)
  (hr₁₁ : r₁.Matches s₁₁) (hr₁₂ : r₂.Matches s₁₂)
  (hr₂₁ : r₁.Matches s₂₁) (hr₂₂ : r₂.Matches s₂₂)
  (h₁ : ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₁₂ ∧ r₁.Matches (s₁₁ ++ s₃) ∧ r₂.Matches s₄))
  (h₂ : ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂₂ ∧ r₁.Matches (s₂₁ ++ s₃) ∧ r₂.Matches s₄)) :
  s₁₁ = s₂₁ ∧ s₁₂ = s₂₂ := by
  rw [List.append_eq_append_iff] at hs
  cases hs with
  | inl hs =>
    rcases hs with ⟨as, hs⟩
    simp_all
    cases as with
    | nil => rfl
    | cons x xs =>
      exact absurd hr₂₂ (h₁ (x::xs) (by simp) s₂₂ rfl hr₂₁)
  | inr hs =>
    rcases hs with ⟨as, hs⟩
    simp_all
    cases as with
    | nil => rfl
    | cons x xs =>
      exact absurd hr₁₂ (h₂ (x::xs) (by simp) s₁₂ rfl hr₁₁)

theorem POSIX.unique {r : Regex α} {p₁ p₂ : Parse r} (hp : p₁.flat = p₂.flat) (h₁ : POSIX p₁) (h₂ : POSIX p₂) :
  p₁ = p₂ := by
  induction h₁ with
  | epsilon =>
    cases h₂
    rfl
  | char c =>
    cases h₂
    rfl
  | left h₁ ih =>
    cases h₂ with
    | left h₂ =>
      rw [left.injEq]
      simp at hp
      exact ih hp h₂
    | right h₂ hn =>
      simp at hp
      rw [←hp] at hn
      exact absurd h₁.matches hn
  | right h₁ hn ih =>
    cases h₂ with
    | left h₂ =>
      simp at hp
      rw [hp] at hn
      exact absurd h₂.matches hn
    | right h₂ hn' =>
      rw [right.injEq]
      simp at hp
      exact ih hp h₂
  | mul h₁₁ h₁₂ hs₁ ih₁ ih₂ =>
    cases h₂ with
    | mul h₂₁ h₂₂ hs₂ =>
      simp at hp
      have hv' := longest_split_unique hp h₁₁.matches h₁₂.matches h₂₁.matches h₂₂.matches hs₁ hs₂
      rw [ih₁ hv'.left h₂₁, ih₂ hv'.right h₂₂]
  | star_nil =>
    cases h₂ with
    | star_nil => rfl
    | star_cons _ _ hp' =>
      simp at hp
      exact absurd hp.left hp'
  | star_cons h₁₁ h₁₂ hp₁ hs₁ ih₁ ih₂ =>
    cases h₂ with
    | star_nil =>
      simp at hp
      exact absurd hp.left hp₁
    | star_cons h₂₁ h₂₂ hp₂ hs₂ =>
      simp at hp
      have hv' := longest_split_unique hp h₁₁.matches h₁₂.matches h₂₁.matches h₂₂.matches hs₁ hs₂
      have ih₂ := ih₂ hv'.right h₂₂
      simp at ih₂
      rw [ih₁ hv'.left h₂₁, ih₂]
