import RegexPosix.Value
import RegexPosix.POSIX
import RegexPosix.Lexer

universe u

variable {α : Type u}

open RegularExpression

theorem matchEpsilon_iff (r : RegularExpression α) :
  [] ∈ r.matches' ↔ r.matchEpsilon := by
  induction r with
  | zero => simp [matchEpsilon]
  | epsilon => simp [matchEpsilon]
  | char =>
    simp [matchEpsilon]
    intro h
    cases h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp [matchEpsilon]
    rw [←ih₁, ←ih₂]
    rfl
  | comp r₁ r₂ ih₁ ih₂ =>
    simp [matchEpsilon]
    rw [←ih₁, ←ih₂]
    constructor
    · intro h
      let ⟨u, hu, v, hv, huv⟩ := h
      simp at huv
      rw [huv.left] at hu
      rw [huv.right] at hv
      exact ⟨hu, hv⟩
    · intro h
      exact ⟨[], h.left, [], h.right, rfl⟩
  | star r ih =>
    simp [matchEpsilon]
    apply Language.nil_mem_kstar

-- Lemma 2
theorem nullable_posix (r : RegularExpression α) (hr : r.matchEpsilon) :
  POSIX [] r (mkeps ⟨r, hr⟩).fst := by
  induction r with
  | zero => simp [matchEpsilon] at hr
  | epsilon =>
    simp only [mkeps]
    apply POSIX.epsilon
  | char => simp [matchEpsilon] at hr
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [mkeps]
    simp [matchEpsilon] at hr
    cases hr with
    | inl hr =>
      simp [hr]
      apply ih₁ at hr
      apply POSIX.left
      exact hr
    | inr hr =>
      by_cases hr' : r₁.matchEpsilon
      · simp [hr']
        apply ih₁ at hr'
        apply POSIX.left
        exact hr'
      · simp [hr']
        apply ih₂ at hr
        apply POSIX.right
        exact hr
        simp at hr'
        contrapose hr'
        simp at *
        rw [matchEpsilon_iff] at hr'
        exact hr'
  | comp r₁ r₂ ih₁ ih₂ =>
    simp [matchEpsilon] at hr
    let ⟨hr₁, hr₂⟩ := hr
    apply ih₁ at hr₁
    apply ih₂ at hr₂
    simp only [mkeps]
    apply POSIX_mul_nil
    exact hr₁
    exact hr₂
  | star r ih =>
    simp only [mkeps]
    apply POSIX.star_nil

variable [DecidableEq α]

theorem matches_deriv (r : RegularExpression α) (x : α) (xs : List α) :
  x::xs ∈ r.matches' ↔ xs ∈ (r.deriv x).matches' := by
  induction r generalizing xs with
  | zero => simp
  | epsilon => simp
  | char c =>
    simp [deriv]
    constructor
    · intro h
      cases h
      simp
    · intro h
      split_ifs at h with hc
      · cases h
        rw [hc]
        ext
        rfl
      · cases h
  | plus r₁ r₂ ih₁ ih₂ =>
    simp
    constructor
    · intro h
      cases h with
      | inl h =>
        rw [ih₁] at h
        exact Or.inl h
      | inr h =>
        rw [ih₂] at h
        exact Or.inr h
    · intro h
      cases h with
      | inl h =>
        rw [←ih₁] at h
        exact Or.inl h
      | inr h =>
        rw [←ih₂] at h
        exact Or.inr h
  | comp r₁ r₂ ih₁ ih₂ =>
    constructor
    · intro h
      simp at h
      let ⟨a, ha, b, hb, hab⟩ := h
      simp at hab
      cases a with
      | nil =>
        simp at hab
        rw [hab] at hb
        rw [ih₂] at hb
        rw [matchEpsilon_iff] at ha
        simp [deriv, ha]
        exact Or.inr hb
      | cons y ys =>
        simp at hab
        rw [hab.left] at ha
        rw [ih₁] at ha
        simp [deriv]
        split_ifs
        · exact Or.inl ⟨ys, ha, b, hb, hab.right⟩
        · exact ⟨ys, ha, b, hb, hab.right⟩
    · intro h
      simp [deriv] at h
      split_ifs at h with hr₁
      · simp at h
        cases h with
        | inl h =>
          let ⟨a, ha, b, hb, hab⟩ := h
          rw [←ih₁] at ha
          simp at hab
          rw [←hab]
          exact ⟨x::a, ha, b, hb, rfl⟩
        | inr h =>
          rw [←matchEpsilon_iff] at hr₁
          rw [←ih₂] at h
          exact ⟨[], hr₁, x::xs, h, rfl⟩
      · let ⟨a, ha, b, hb, hab⟩ := h
        rw [←ih₁] at ha
        simp at hab
        rw [←hab]
        exact ⟨x::a, ha, b, hb, rfl⟩
  | star => sorry

-- Lemma 3
theorem posix_deriv (s : List α) (r : RegularExpression α) (v : Value α) (c : α) (h : POSIX s (r.deriv c) v) :
  POSIX (c::s) r (inj r c ⟨v, POSIX_inhab h⟩).fst := by
  induction r generalizing v s with
  | zero =>
    simp at h
    cases h
  | epsilon =>
    simp at h
    cases h
  | char d =>
    simp [deriv] at h
    split_ifs at h with hc
    · cases h
      simp [hc] at h
      simp [inj, hc]
      apply POSIX.char
    · cases h
  | plus r₁ r₂ ih₁ ih₂ =>
    match v with
    | Value.left v' =>
      cases h with
      | left _ _ _ _ h =>
        apply ih₁ at h
        apply POSIX.left
        exact h
    | Value.right v' =>
      cases h with
      | right _ _ _ _ h hn =>
        apply ih₂ at h
        apply POSIX.right
        exact h
        rw [matches_deriv]
        exact hn
  | comp r₁ r₂ ih₁ ih₂ =>
    simp [deriv] at h
    split_ifs at h with hn
    · cases h with
      | left _ _ _ v' h' =>
        simp [hn] at h
        cases h' with
        | mul => sorry
      | right _ _ _ v' h' hn' =>
        simp [hn] at h
        apply ih₂ at h'
        sorry
    · cases h with
      | mul s₁ s₂ _ _ v₁ v₂ h₁ h₂ hn' =>
        simp_rw [←matches_deriv] at hn'
        simp [hn] at h
        apply ih₁ at h₁
        sorry
  | star => sorry

-- Theorem 2 Part 1
theorem lexer_none_iff (s : List α) (r : RegularExpression α) :
  s ∉ r.matches' ↔ lexer r s = none := by
  induction s generalizing r with
  | nil =>
    simp [lexer]
    rw [matchEpsilon_iff]
    simp
  | cons x xs ih =>
    constructor
    · intro h
      rw [matches_deriv] at h
      rw [ih] at h
      simp [lexer]
      rw [h]
    · intro h
      simp [lexer] at h
      generalize h' : lexer (r.deriv x) xs = v
      rw [h'] at h
      cases v with
      | none =>
        rw [←ih] at h'
        contrapose h'
        simp at *
        rw [matches_deriv] at h'
        exact h'
      | some => simp at h

-- Theorem 2 Part 2
theorem lexer_some_iff (s : List α) (r : RegularExpression α) :
  s ∈ r.matches' ↔ ∃ v, lexer r s = some v ∧ POSIX s r v.fst := by
  induction s generalizing r with
  | nil =>
    rw [matchEpsilon_iff]
    constructor
    · intro h
      have := nullable_posix r h
      use mkeps ⟨r, h⟩
      constructor
      · simp [lexer]
        exact h
      · exact this
    · intro ⟨v, h₁, h₂⟩
      simp [lexer] at h₁
      let ⟨h, _⟩ := h₁
      exact h
  | cons x xs ih =>
    constructor
    · intro h
      rw [matches_deriv] at h
      rw [ih] at h
      let ⟨v, h₁, h₂⟩ := h
      have h := posix_deriv xs r v.fst x h₂
      use (inj r x ⟨v.fst, POSIX_inhab h₂⟩)
      constructor
      · simp [lexer, h₁]
      · exact h
    · intro ⟨v, h₁, h₂⟩
      apply correctness at h₂
      exact h₂.left

-- Corollary 1 Part 1
theorem lexer_posix_none_iff (r : RegularExpression α) (s : List α) :
  lexer r s = none ↔ ¬(∃ v, POSIX s r v) := by
  constructor
  · intro h
    rw [←lexer_none_iff] at h
    contrapose h
    simp at *
    let ⟨v, h⟩ := h
    apply correctness at h
    exact h.left
  · intro h
    rw [←lexer_none_iff]
    contrapose h
    simp at *
    rw [lexer_some_iff] at h
    let ⟨v, h₁, h₂⟩ := h
    use v.fst

-- Corollary 1 Part 2
theorem lexer_posix_some_iff (r : RegularExpression α) (s : List α) (v : Σ' v : Value α, Inhab v r) :
  lexer r s = some v ↔ POSIX s r v.fst := by
  constructor
  · intro h
    by_cases hs : s ∈ r.matches'
    · rw [lexer_some_iff] at hs
      let ⟨v', h₁, h₂⟩ := hs
      -- use uniqueness of posix values
      sorry
    · rw [lexer_none_iff] at hs
      -- absurd by h and hs
      sorry
  · intro h
    have := correctness _ _ _ h
    let ⟨hs, _⟩ := this
    rw [lexer_some_iff] at hs
    let ⟨v', h₁, h₂⟩ := hs
    have := uniqueness _ _ _ _ ⟨h, h₂⟩
    -- Need to show uniqueness of inhabition
    sorry
