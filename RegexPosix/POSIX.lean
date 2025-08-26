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
    ¬(∃ s₃ s₄, v₁.flat ++ v₂.flat = s₃ ++ s₄ ∧ v₁.flat.length < s₃.length ∧ r₁.Matches s₃ ∧ r₂.Matches s₄) →
    POSIX (mul r₁ r₂) (seq v₁ v₂)
  | star_nil {r : Regex α} :
    POSIX (star r) (stars [])
  | stars {r : Regex α} {v : Value α} {vs : List (Value α)} :
    POSIX r v →
    POSIX (star r) (stars vs) →
    v.flat ≠ [] →
    ¬(∃ s₃ s₄, v.flat ++ (stars vs).flat = s₃ ++ s₄ ∧ v.flat.length < s₃.length ∧ r.Matches s₃ ∧ (star r).Matches s₄) →
    POSIX (star r) (stars (v::vs))

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

theorem longest_split_unique {r₁ r₂ : Regex α} {s₁₁ s₁₂ s₂₁ s₂₂ : List α}
  (hs : s₁₁ ++ s₁₂ = s₂₁ ++ s₂₂)
  (hr₁₁ : r₁.Matches s₁₁) (hr₁₂ : r₂.Matches s₁₂)
  (hr₂₁ : r₁.Matches s₂₁) (hr₂₂ : r₂.Matches s₂₂)
  (h₁ : ¬(∃ s₃ s₄, s₁₁ ++ s₁₂ = s₃ ++ s₄ ∧ s₁₁.length < s₃.length ∧ r₁.Matches s₃ ∧ r₂.Matches s₄))
  (h₂ : ¬(∃ s₃ s₄, s₂₁ ++ s₂₂ = s₃ ++ s₄ ∧ s₂₁.length < s₃.length ∧ r₁.Matches s₃ ∧ r₂.Matches s₄)) :
  s₁₁ = s₂₁ ∧ s₁₂ = s₂₂ := by
  rw [List.append_eq_append_iff] at hs
  cases hs with
  | inl hs =>
    rcases hs with ⟨as, hs⟩
    simp_all
    cases as with
    | nil => rfl
    | cons x xs =>
      simp_all
      exact absurd hr₂₂ (h₁ (s₁₁ ++ x :: xs) s₂₂ (by simp) (by simp) hr₂₁)
  | inr hs =>
    rcases hs with ⟨as, hs⟩
    simp_all
    cases as with
    | nil => rfl
    | cons x xs =>
      simp_all
      exact absurd hr₁₂ (h₂ (s₂₁ ++ x::xs) s₁₂ (by simp) (by simp) hr₁₁)

theorem List.prefix_lt {s₁ s₂ s₃ s₄ : List α} :
  s₁ ++ s₂ = s₃ ++ s₄ →
  s₁.length < s₃.length →
  ∃ s₃₁ s₃₂, s₃₁ ++ s₃₂ = s₃ ∧ s₃₁ = s₁ := by
  intro hs hs₃
  induction s₁ generalizing s₃ with
  | nil =>
    simp at hs hs₃
    exact ⟨[], s₃, by simp, rfl⟩
  | cons x xs ih =>
    cases s₃ with
    | nil => simp at hs₃
    | cons y ys =>
      simp at hs hs₃
      cases hs.left
      rcases ih hs.right hs₃ with ⟨s₃₁, s₃₂, hs₃', hxs⟩
      subst hxs hs₃'
      exact ⟨x::s₃₁, s₃₂, by simp, rfl⟩

theorem longest_split_iff {P₁ P₂ : List α → Prop} {s₁ s₂ : List α} :
  (¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ P₁ (s₁ ++ s₃) ∧ P₂ s₄)) ↔
  (¬(∃ s₃ s₄, s₁ ++ s₂ = s₃ ++ s₄ ∧ s₁.length < s₃.length ∧ P₁ s₃ ∧ P₂ s₄)) := by
  simp
  constructor
  · intro h s₃ s₄ hs hs₃ hp
    rcases List.prefix_lt hs hs₃ with ⟨s₃₁, s₃₂, hs₃', hs₁⟩
    subst hs₁ hs₃'
    simp [List.length_pos_iff] at hs₃
    simp at hs
    exact h s₃₂ hs₃ s₄ hs.symm hp
  · intro h s₃ hs₃ s₄ hs₂ hp
    rw [←ne_eq, List.ne_nil_iff_length_pos] at hs₃
    exact h (s₁ ++ s₃) s₄ (by simp [hs₂]) (by simp [hs₃]) hp

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
