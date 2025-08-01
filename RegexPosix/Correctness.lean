import RegexPosix.POSIX
import RegexPosix.Parse

open Regex
open Value

universe u

variable {α : Type u}

theorem mkeps_posix {r : Regex α} (hn : r.nullable) :
  POSIX r (r.mkeps hn).fst := by
  induction r with
  | emptyset => simp [nullable] at hn
  | epsilon =>
    simp only [mkeps]
    apply POSIX.epsilon
  | char => simp [nullable] at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp only [mkeps]
    split_ifs with hn'
    · exact POSIX.left (ih₁ hn')
    · refine POSIX.right (ih₂ (Or.resolve_left hn hn')) ?_
      rw [mkeps_flat]
      rw [←nullable_iff_matches_nil]
      exact hn'
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp only [mkeps]
    refine POSIX.mul (ih₁ hn.left) (ih₂ hn.right) ?_
    rw [mkeps_flat]
    simp_all
  | star r ih =>
    simp only [mkeps]
    apply POSIX.star_nil

variable [DecidableEq α]

theorem inj_posix {r : Regex α} {v : Value α} {c : α} (h : POSIX (r.deriv c) v) :
  POSIX r (inj r c ⟨v, h.inhab⟩).fst := by
  induction r generalizing v with
  | emptyset =>
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
      simp [inj]
      exact POSIX.char d
    · cases h
  | plus r₁ r₂ ih₁ ih₂ =>
    match v with
    | Value.left v' =>
      cases h with
      | left h =>
        simp [inj]
        exact POSIX.left (ih₁ h)
    | Value.right v' =>
      cases h with
      | right h hn =>
        simp [inj]
        refine POSIX.right (ih₂ h) ?_
        rw [inj_flat, Matches_deriv]
        exact hn
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [deriv] at h
    split_ifs at h with hn
    · cases h with
      | left h' =>
        simp [hn] at h
        cases h' with
        | mul h₁ h₂ hs =>
          simp [inj, hn]
          refine POSIX.mul (ih₁ h₁) h₂ ?_
          simp_rw [inj_flat, List.cons_append, Matches_deriv]
          exact hs
      | right h' hn' =>
        simp [inj, hn]
        refine POSIX.mul (mkeps_posix hn) (ih₂ h') ?_
        simp
        intro x hx y hxy hr₁ hr₂
        rw [inj_flat] at hxy
        simp [mkeps_flat] at hr₁
        rw [List.append_eq_cons_iff] at hxy
        simp [hx] at hxy
        rcases hxy with ⟨z, hx, hs⟩
        rw [hx, Matches_deriv] at hr₁
        rw [hs] at hn'
        exact absurd (Matches.mul rfl hr₁ hr₂) hn'
    · cases h with
      | mul h₁ h₂ hn' =>
        simp [inj, hn]
        refine POSIX.mul (ih₁ h₁) h₂ ?_
        simp_rw [inj_flat, List.cons_append, Matches_deriv]
        exact hn'
  | star r ih =>
    match v with
    | Value.seq v (Value.stars vs) =>
      simp [inj]
      cases h with
      | mul h₁ h₂ hs =>
        refine POSIX.stars (ih h₁) h₂ (by simp [inj_flat]) ?_
        simp_rw [inj_flat, List.cons_append, Matches_deriv]
        exact hs

theorem injs_posix {r : Regex α} {v : Value α} {s : List α} (h : POSIX (r.derivs s) v) :
  POSIX r (injs r s ⟨v, h.inhab⟩).fst := by
  induction s generalizing r with
  | nil =>
    rw [derivs] at h
    exact h
  | cons x xs ih =>
    rw [derivs] at h
    simp [injs]
    apply inj_posix
    exact ih h

theorem matches_parse_posix_iff {r : Regex α} {s : List α} :
  r.Matches s ↔ ∃ v, r.parse s = some v ∧ POSIX r v := by
  simp [parse]
  rw [Matches_derivs, ←nullable_iff_matches_nil]
  constructor
  · intro h
    exact ⟨h, injs_posix (mkeps_posix h)⟩
  · intro ⟨h, _⟩
    exact h

theorem parse_posix_iff (r : Regex α) (s : List α) (v : Value α) :
  r.parse s = some v ↔ v.flat = s ∧ POSIX r v := by
  constructor
  · intro h
    refine ⟨parse_flat h, ?_⟩
    simp [parse] at h
    rcases h with ⟨hn, h⟩
    rw [←h]
    exact injs_posix (mkeps_posix hn)
  · intro ⟨hv, h⟩
    subst hv
    rcases (matches_parse_posix_iff.mp h.matches) with ⟨v', h', h''⟩
    rw [POSIX.unique (parse_flat h') h'' h] at h'
    exact h'
