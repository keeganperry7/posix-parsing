import RegexPosix.POSIX
import RegexPosix.Parse

open Regex
open Value

universe u

variable {α : Type u}

-- theorem posix_mkeps {r : Regex α} {v : Value α} (hv : v.flat = []) :
--   (∃ hn, (r.mkeps hn).fst = v) ↔ POSIX r v := by
--   induction r with
--   | emptyset => exact ⟨nofun, nofun⟩
--   | epsilon =>
--     simp [mkeps]
--     constructor
--     · intro h
--       subst h
--       exact POSIX.epsilon
--     · intro h
--       cases h
--       rfl
--   | char c =>
--     constructor
--     · nofun
--     · intro h
--       cases h
--       simp at hv
--   | plus r₁ r₂ ih₁ ih₂ =>
--     constructor
--     · sorry
--     · sorry
--   | mul r₁ r₂ => sorry
--   | star r => sorry

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
    · apply POSIX.right
      exact ih₂ (Or.resolve_left hn hn')
      rw [mkeps_flat]
      rw [←nullable_iff_matches_nil]
      exact hn'
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp only [mkeps]
    apply POSIX.mul
    exact ih₁ hn.left
    exact ih₂ hn.right
    rw [mkeps_flat]
    simp_all
  | star r ih =>
    simp only [mkeps]
    apply POSIX.star_nil

variable [DecidableEq α]

theorem deriv_posix' (r : Regex α) (v v' : Value α) (c : α) (hv : v.flat = c::v'.flat) (hv' : POSIX (r.deriv c) v') :
  (inj r c ⟨v', hv'.inhab⟩).fst = v ↔ POSIX r v := by
  induction r generalizing v v' with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon =>
    constructor
    · nofun
    · intro h
      cases h
      simp at hv
  | char d =>
    constructor
    · intro h
      simp at hv'
      split_ifs at hv' with hc
      · subst hc
        simp at hv'
        cases hv'
        simp [inj] at h
        subst h
        exact POSIX.char c
      · nomatch v'
    · intro h
      cases h
      simp at hv
      cases hv.left
      simp [inj]
  | plus r₁ r₂ ih₁ ih₂ =>
    cases hv' with
    | left hv' =>
      simp [inj]
      constructor
      · intro h
        subst h
        apply POSIX.left
        rw [←ih₁]
        simp [inj_flat]
        exact hv'
      · intro h
        cases h with
        | left h =>
          simp at hv
          rw [left.injEq, ih₁ _ _ hv hv']
          exact h
        | right h hn =>
          simp at hv
          rw [hv] at hn
          exact absurd (Matches_deriv.mpr (POSIX_matches hv')) hn
    | right hv' hn =>
      simp [inj]
      constructor
      · intro h
        subst h
        apply POSIX.right
        rw [←ih₂]
        simp [inj_flat]
        exact hv'
        simp at hv
        rw [←Matches_deriv, ←hv] at hn
        exact hn
      · intro h
        cases h with
        | left h =>
          simp at hv
          rw [←Matches_deriv, ←hv] at hn
          exact absurd (POSIX_matches h) hn
        | right h hn' =>
          simp at hv
          rw [right.injEq, ih₂ _ _ hv hv']
          exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    sorry
  | star r ih =>
    match v' with
    | Value.seq v' (Value.stars vs') =>
      simp [inj]
      cases hv' with
      | mul h₁ h₂ hn =>
        constructor
        · intro h
          subst h
          apply POSIX.stars
          rw [←ih]
          simp [inj_flat]
          exact h₁
          exact h₂
          simp [inj_flat]
          simp_rw [inj_flat, List.cons_append, Matches_deriv]
          exact hn
        · sorry

theorem derivs_posix' (r : Regex α) (v v' : Value α) (s : List α) (hv : v.flat = s ++ v'.flat) (hv' : POSIX (r.derivs s) v') :
  (injs r s ⟨v', hv'.inhab⟩).fst = v ↔ POSIX r v := by
  induction s generalizing r v with
  | nil =>
    simp [injs]
    simp at hv
    simp at hv'
    constructor
    · intro h
      subst h
      exact hv'
    · intro h
      exact POSIX_unique (hv.symm) hv' h
  | cons x xs ih =>
    simp [injs]
    rw [deriv_posix']
    simp [injs_flat, hv]
    rw [←ih _ _ (by simp [injs_flat]) hv']

theorem deriv_posix (r : Regex α) (v : Value α) (c : α) (hv : Inhab v (r.deriv c)) :
  POSIX (r.deriv c) v ↔ POSIX r (inj r c ⟨v, hv⟩).fst := by
  induction r generalizing v with
  | emptyset => nomatch hv
  | epsilon => nomatch hv
  | char d =>
    simp [deriv] at hv
    split_ifs at hv with hc
    · cases hv
      simp [hc] at hv
      simp [inj, hc]
      exact ⟨fun _ => POSIX.char d, fun _ => POSIX.epsilon⟩
    · nomatch hv
  | plus r₁ r₂ ih₁ ih₂ =>
    cases hv with
    | left hv =>
      simp [inj]
      constructor
      · intro h
        cases h with
        | left h =>
          rw [ih₁ _ hv] at h
          exact POSIX.left h
      · intro h
        cases h with
        | left h =>
          rw [←ih₁ _ hv] at h
          exact POSIX.left h
    | right hv =>
      simp [inj]
      constructor
      · intro h
        cases h with
        | right h hn =>
          rw [ih₂ _ hv] at h
          rw [←Matches_deriv] at hn
          refine POSIX.right h ?_
          rw [inj_flat]
          exact hn
      · intro h
        cases h with
        | right h hn =>
          rw [←ih₂ _ hv] at h
          rw [inj_flat, Matches_deriv] at hn
          exact POSIX.right h hn
  | mul r₁ r₂ ih₁ ih₂ =>
    simp [deriv]
    split_ifs with hr₁
    · simp [hr₁] at hv
      simp [inj, hr₁]
      split
      · constructor
        · intro h
          match h with
          | POSIX.left (POSIX.mul h₁ h₂ hn) =>
            rw [ih₁ _ (inhab_seq_fst (inhab_left hv))] at h₁
            refine POSIX.mul h₁ h₂ ?_
            simp_rw [inj_flat, List.cons_append, Matches_deriv]
            exact hn
        · intro h
          cases h with
          | mul h₁ h₂ hn =>
            rw [←ih₁ _ (inhab_seq_fst (inhab_left hv))] at h₁
            simp_rw [inj_flat, List.cons_append, Matches_deriv] at hn
            exact POSIX.left (POSIX.mul h₁ h₂ hn)
      · constructor
        · intro h
          cases h with
          | right h hn =>
            rw [ih₂ _ (inhab_right hv)] at h
            refine POSIX.mul (mkeps_posix hr₁) h ?_
            simp
            intro x hx y hxy hr₁ hr₂
            rw [inj_flat] at hxy
            simp [mkeps_flat] at hr₁
            rw [List.append_eq_cons_iff] at hxy
            simp [hx] at hxy
            rcases hxy with ⟨z, hx, hs⟩
            rw [hx] at hr₁
            rw [Matches_deriv] at hr₁
            rw [hs] at hn
            exact absurd (Matches.mul rfl hr₁ hr₂) hn
        · intro h
          cases h with
          | mul h₁ h₂ hn =>
            rw [←ih₂ _ (inhab_right hv)] at h₂
            refine POSIX.right h₂ ?_
            simp_rw [inj_flat, mkeps_flat] at hn
            intro h
            rename_i v₂ _
            generalize hs : v₂.flat = s at h
            cases h with
            | @mul s₁ s₂ _ _ _ hs' h₁' h₂' =>
              subst hs
              rw [←Matches_deriv] at h₁'
              simp at hn
              exact absurd h₂' (hn (c::s₁) (by simp) s₂ (by simp [hs']) h₁')
    · simp [hr₁] at hv
      simp [inj, hr₁]
      split
      constructor
      · intro h
        cases h with
        | mul h₁ h₂ hn =>
          rw [ih₁ _ (inhab_seq_fst hv)] at h₁
          refine POSIX.mul h₁ h₂ ?_
          simp_rw [inj_flat, List.cons_append, Matches_deriv]
          exact hn
      · intro h
        cases h with
        | mul h₁ h₂ hn =>
          rw [←ih₁ _ (inhab_seq_fst hv)] at h₁
          simp_rw [inj_flat, List.cons_append, Matches_deriv] at hn
          exact POSIX.mul h₁ h₂ hn
  | star r ih =>
    match v with
    | Value.seq v (Value.stars vs) =>
      simp [inj]
      constructor
      · intro h
        cases h with
        | mul h₁ h₂ hs =>
          rw [ih _ (inhab_seq_fst hv)] at h₁
          refine POSIX.stars h₁ h₂ ?_ ?_
          simp [inj_flat]
          simp_rw [inj_flat, List.cons_append, Matches_deriv]
          exact hs
      · intro h
        cases h with
        | stars h₁ h₂ hs hn =>
          rw [←ih _ (inhab_seq_fst hv)] at h₁
          refine POSIX.mul h₁ h₂ ?_
          simp_rw [inj_flat, List.cons_append, Matches_deriv] at hn
          exact hn

theorem derivs_posix (r : Regex α) (v : Value α) (s : List α) (hv : Inhab v (r.derivs s)) :
  POSIX (r.derivs s) v ↔ POSIX r (injs r s ⟨v, hv⟩).fst := by
  induction s generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp [injs]
    rw [←deriv_posix]
    exact ih _ hv

theorem parse_posix_iff (r : Regex α) (s : List α) (v : Value α) (hv : v.flat = s) :
  r.parse s = some v ↔ POSIX r v := by
  rw [parse]
  subst hv
  split_ifs with hn
  · rw [Option.some.injEq, derivs_posix']
    simp [mkeps_flat]
    exact mkeps_posix hn
  · rw [false_iff]
    intro h
    rw [nullable_iff_matches_nil, ←Matches_derivs] at hn
    exact absurd (POSIX_matches h) hn

theorem parse_posix (r : Regex α) (s : List α) (v : Value α) (h : r.parse s = some v) :
  POSIX r v := by
  induction s generalizing r v with
  | nil =>
    simp [parse, injs] at h
    rcases h with ⟨hn, h⟩
    rw [←h]
    exact mkeps_posix hn
  | cons x xs ih =>
    simp [parse, injs] at h
    rcases h with ⟨hn, h⟩
    rw [←h, ←deriv_posix]
    apply ih
    simp [parse, hn]
