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
    @POSIX (r₁.plus r₂) p.right
  | mul {r₁ r₂ : Regex α} {p₁ : Parse r₁} {p₂ : Parse r₂} :
    POSIX p₁ →
    POSIX p₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = p₂.flat ∧ r₁.Matches (p₁.flat ++ s₃) ∧ r₂.Matches s₄) →
    POSIX (p₁.seq p₂)
  | star_nil {r : Regex α} :
    ¬r.nullable →
    @POSIX r.star star_nil
  | star_nil_null {r : Regex α} {p : Parse r} :
    r.nullable →
    POSIX p →
    p.flat = [] →
    POSIX (p.star_cons star_nil)
  | stars {r : Regex α} {p : Parse r} {ps : Parse (star r)} :
    POSIX p →
    POSIX ps →
    p.flat ≠ [] →
    ps.flat ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = ps.flat ∧ r.Matches (p.flat ++ s₃) ∧ (star r).Matches s₄) →
    POSIX (p.star_cons ps)
  | stars_tail_empty {r : Regex α} {p : Parse r} {ps : Parse (star r)} :
    POSIX p →
    POSIX ps →
    p.flat ≠ [] →
    ps.flat = [] →
    POSIX (p.star_cons star_nil)

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
  | star_nil hn =>
    cases h₂ with
    | star_nil => rfl
    | star_nil_null => contradiction
    | stars _ _ hp' =>
      simp at hp
      exact absurd hp.left hp'
    | stars_tail_empty =>
      simp at hp
      contradiction
  | star_nil_null hn hp₁ hp₁_flat ih =>
    cases h₂ with
    | star_nil => contradiction
    | star_nil_null _ hp₂ =>
      simp at hp
      simp
      exact ih hp hp₂
    | stars => simp_all
    | stars_tail_empty => simp_all
  | stars h₁₁ h₁₂ hp₁ hp₂ hs₁ ih₁ ih₂ =>
    cases h₂ with
    | star_nil =>
      simp at hp
      exact absurd hp.left hp₁
    | star_nil_null => simp_all
    | stars h₂₁ h₂₂ hp₂ _ hs₂ =>
      simp at hp
      have hv' := longest_split_unique hp h₁₁.matches h₁₂.matches h₂₁.matches h₂₂.matches hs₁ hs₂
      have ih₂ := ih₂ hv'.right h₂₂
      simp at ih₂
      rw [ih₁ hv'.left h₂₁, ih₂]
    | stars_tail_empty h₂₁ h₂₂ hp₂₁ hp₂₂ =>
      simp only [flat] at hp
      have hk := longest_split_unique hp h₁₁.matches h₁₂.matches h₂₁.matches (hp₂₂ ▸ h₂₂.matches) hs₁ (by simp)
      simp_all
  | stars_tail_empty h₁₁ h₁₂ hp₁₁ hp₁₂ ih₁ ih₂ =>
    cases h₂ with
    | star_nil => simp_all
    | star_nil_null => simp_all
    | stars h₂₁ h₂₂ hp₂₁ hp₂₂ hs =>
      simp only [flat] at hp
      have hk := longest_split_unique hp.symm h₂₁.matches h₂₂.matches h₁₁.matches (hp₁₂ ▸ h₁₂.matches) hs (by simp)
      simp_all
    | stars_tail_empty h₂₁ h₂₂ hp₂₁ hp₂₂ =>
      simp at hp
      simp [ih₁ hp h₂₁]
