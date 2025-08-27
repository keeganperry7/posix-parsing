import RegexPosix.Value

open Regex
open Value

universe u

variable {α : Type u}

inductive POSIX : Regex α → Value α → Prop
  | epsilon : POSIX epsilon empty
  | char (c : α) : POSIX (char c) (char c)
  | left {r₁ r₂ : Regex α} {v : Value α} :
    POSIX r₁ v →
    POSIX (plus r₁ r₂) (left v)
  | right {r₁ r₂ : Regex α} {v : Value α} :
    POSIX r₂ v →
    ¬r₁.Matches v.flat →
    POSIX (plus r₁ r₂) (right v)
  | mul {r₁ r₂ : Regex α} {v₁ v₂ : Value α} :
    POSIX r₁ v₁ →
    POSIX r₂ v₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = v₂.flat ∧ r₁.Matches (v₁.flat ++ s₃) ∧ r₂.Matches s₄) →
    POSIX (mul r₁ r₂) (seq v₁ v₂)
  | star_nil {r : Regex α} :
    POSIX (star r) (stars [])
  | stars {r : Regex α} {v : Value α} {vs : List (Value α)} :
    POSIX r v →
    POSIX (star r) (stars vs) →
    v.flat ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = (stars vs).flat ∧ r.Matches (v.flat ++ s₃) ∧ (star r).Matches s₄) →
    POSIX (star r) (stars (v::vs))

inductive POSIX' : {r : Regex α} → Parse r → Prop
  | epsilon : POSIX' Parse.empty
  | char (c : α) : POSIX' (Parse.char c)
  | left {r₁ : Regex α} {p : Parse r₁} :
    POSIX' p →
    POSIX' p.left
  | right {r₁ r₂ : Regex α} {p : Parse r₂} :
    POSIX' p →
    ¬r₁.Matches p.flat →
    @POSIX' (r₁.plus r₂) p.right
  | mul {r₁ r₂ : Regex α} {p₁ : Parse r₁} {p₂ : Parse r₂} :
    POSIX' p₁ →
    POSIX' p₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = p₂.flat ∧ r₁.Matches (p₁.flat ++ s₃) ∧ r₂.Matches s₄) →
    POSIX' (p₁.seq p₂)
  | star_nil :
    POSIX' Parse.star_nil
  | stars {r : Regex α} {p : Parse r} {ps : Parse (star r)} :
    POSIX' p →
    POSIX' ps →
    p.flat ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = ps.flat ∧ r.Matches (p.flat ++ s₃) ∧ (star r).Matches s₄) →
    POSIX' (p.star_cons ps)

theorem POSIX.inhab {r : Regex α} {v : Value α} : POSIX r v → Inhab v r
  | epsilon => Inhab.empty
  | char c => Inhab.char c
  | left h => Inhab.left (inhab h)
  | right h hn => Inhab.right (inhab h)
  | mul h₁ h₂ hn => Inhab.seq (inhab h₁) (inhab h₂)
  | star_nil => Inhab.star_nil
  | stars h₁ h₂ hv hn => Inhab.stars (inhab h₁) (inhab h₂)

theorem POSIX.matches {r : Regex α} {v : Value α} : POSIX r v → r.Matches v.flat :=
  fun h => h.inhab.matches

theorem POSIX'.matches {r : Regex α} {p : Parse r} : POSIX' p → r.Matches p.flat :=
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

theorem POSIX'.unique {r : Regex α} {p₁ p₂ : Parse r} (hp : p₁.flat = p₂.flat) (h₁ : POSIX' p₁) (h₂ : POSIX' p₂) :
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
      rw [Parse.left.injEq]
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
      rw [Parse.right.injEq]
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
    | stars _ _ hp' =>
      simp at hp
      exact absurd hp.left hp'
  | stars h₁₁ h₁₂ hp₁ hs₁ ih₁ ih₂ =>
    cases h₂ with
    | star_nil =>
      simp at hp
      exact absurd hp.left hp₁
    | stars h₂₁ h₂₂ hp₂ hs₂ =>
      simp at hp
      have hv' := longest_split_unique hp h₁₁.matches h₁₂.matches h₂₁.matches h₂₂.matches hs₁ hs₂
      have ih₂ := ih₂ hv'.right h₂₂
      simp at ih₂
      rw [ih₁ hv'.left h₂₁, ih₂]

theorem POSIX.unique {r : Regex α} {v₁ v₂ : Value α} (hv : v₁.flat = v₂.flat) (h₁ : POSIX r v₁) (h₂ : POSIX r v₂) :
  v₁ = v₂ := by
  induction h₁ generalizing v₂ with
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
      simp at hv
      exact ih hv h₂
    | right h₂ hn =>
      simp at hv
      rw [←hv] at hn
      exact absurd (POSIX.matches h₁) hn
  | right h₁ hn ih =>
    cases h₂ with
    | left h₂ =>
      simp at hv
      rw [hv] at hn
      exact absurd (POSIX.matches h₂) hn
    | right h₂ hn' =>
      rw [right.injEq]
      simp at hv
      exact ih hv h₂
  | mul h₁₁ h₁₂ hn₁ ih₁ ih₂ =>
    cases h₂ with
    | mul h₂₁ h₂₂ hn₂ =>
      simp at hv
      have hv' := longest_split_unique hv (POSIX.matches h₁₁) (POSIX.matches h₁₂) (POSIX.matches h₂₁) (POSIX.matches h₂₂) hn₁ hn₂
      rw [ih₁ hv'.left h₂₁, ih₂ hv'.right h₂₂]
  | star_nil =>
    cases h₂ with
    | star_nil => rfl
    | stars _ _ hv' =>
      simp at hv
      exact absurd hv.left hv'
  | stars h₁₁ h₁₂ hv' hn₁ ih₁ ih₂ =>
    cases h₂ with
    | star_nil =>
      simp at hv
      exact absurd hv.left hv'
    | stars h₂₁ h₂₂ _ hn₂ =>
      simp at hv
      have hv' := longest_split_unique hv (POSIX.matches h₁₁) (POSIX.matches h₁₂) (POSIX.matches h₂₁) (POSIX.matches h₂₂) hn₁ hn₂
      have ih₂ := ih₂ hv'.right h₂₂
      simp at ih₂
      rw [ih₁ hv'.left h₂₁, ih₂]
