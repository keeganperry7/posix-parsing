import RegexPosix.POSIX
import RegexPosix.Parse

open Regex
open Value

universe u

variable {α : Type u}

theorem mkeps'_posix {r : Regex α} {hn : r.nullable} :
  POSIX' (mkeps' hn) := by
  fun_induction mkeps' with
  | case1 => exact POSIX'.epsilon
  | case2 r₁ r₂ hn hn₁ ih₁ =>
    exact POSIX'.left ih₁
  | case3 r₁ r₂ hn hn₁ hn₂ ih₂ =>
    refine POSIX'.right ih₂ ?_
    rw [mkeps'_flat]
    rw [←nullable_iff_matches_nil]
    exact hn₁
  | case4 r₁ r₂ hn hn₁ hn₂ ih₁ ih₂ =>
    exact POSIX'.mul ih₁ ih₂ (by simp [mkeps'_flat])
  | case5 r hn => exact POSIX'.star_nil

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

theorem inj'_posix {r : Regex α} {c : α} {p : Parse (r.deriv c)} (h : POSIX' p) :
  POSIX' (inj' c p) := by
  fun_induction inj' with
  | case1 d c p =>
    exact POSIX'.char d
  | case2 r₁ r₂ c p ih₁ =>
    cases h with
    | left h =>
      exact POSIX'.left (ih₁ h)
  | case3 r₁ r₂ c p ih₂ =>
    cases h with
    | right h hn =>
      refine POSIX'.right (ih₂ h) ?_
      rw [inj'_flat, Matches.deriv_iff]
      exact hn
  | case4 r₁ r₂ c hn₁ p₁ p₂ p heq ih₁ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    simp [hn₁] at hr
    subst hr heq
    cases h with
    | left h =>
      cases h with
      | mul h₁ h₂ hs =>
        refine POSIX'.mul (ih₁ h₁) h₂ ?_
        simp_rw [inj'_flat, List.cons_append, Matches.deriv_iff]
        exact hs
  | case5 r₁ r₂ c hn₁ p₂ p heq ih₂ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    simp [hn₁] at hr
    subst hr heq
    cases h with
    | right h hn =>
      refine POSIX'.mul (mkeps'_posix) (ih₂ h) ?_
      simp [inj'_flat, mkeps'_flat]
      intro x hx y hxy hr₁ hr₂
      rw [List.append_eq_cons_iff] at hxy
      simp [hx] at hxy
      rcases hxy with ⟨z, hx, hs⟩
      rw [hx, Matches.deriv_iff] at hr₁
      rw [hs] at hn
      exact absurd (Matches.mul rfl hr₁ hr₂) hn
  | case6 r₁ r₂ c hn₁ p₁ p₂ p heq ih₁ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    simp [hn₁] at hr
    subst hr heq
    cases h with
    | mul h₁ h₂ hs =>
      refine POSIX'.mul (ih₁ h₁) h₂ ?_
      simp_rw [inj'_flat, List.cons_append, Matches.deriv_iff]
      exact hs
  | case7 r c p ps ih =>
    cases h with
    | mul h₁ h₂ hs =>
      refine POSIX'.stars (ih h₁) h₂ (by simp [inj'_flat]) ?_
      simp_rw [inj'_flat, List.cons_append, Matches.deriv_iff]
      exact hs

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
        rw [inj_flat, Matches.deriv_iff]
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
          simp_rw [inj_flat, List.cons_append, Matches.deriv_iff]
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
        rw [hx, Matches.deriv_iff] at hr₁
        rw [hs] at hn'
        exact absurd (Matches.mul rfl hr₁ hr₂) hn'
    · cases h with
      | mul h₁ h₂ hn' =>
        simp [inj, hn]
        refine POSIX.mul (ih₁ h₁) h₂ ?_
        simp_rw [inj_flat, List.cons_append, Matches.deriv_iff]
        exact hn'
  | star r ih =>
    match v with
    | Value.seq v (Value.stars vs) =>
      simp [inj]
      cases h with
      | mul h₁ h₂ hs =>
        refine POSIX.stars (ih h₁) h₂ (by simp [inj_flat]) ?_
        simp_rw [inj_flat, List.cons_append, Matches.deriv_iff]
        exact hs

theorem injs'_posix {r : Regex α} {s : List α} {p : Parse (r.derivs s)} (h : POSIX' p) :
  POSIX' (injs' s p) := by
  induction s generalizing r with
  | nil =>
    exact h
  | cons x xs ih =>
    rw [injs']
    exact inj'_posix (ih h)

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

theorem matches_parse'_posix_iff {r : Regex α} {s : List α} :
  r.Matches s ↔ ∃ p, r.parse' s = some p ∧ POSIX' p := by
  simp [parse']
  rw [Matches.derivs_iff, ←nullable_iff_matches_nil]
  constructor
  · intro h
    exact ⟨h, injs'_posix mkeps'_posix⟩
  · intro ⟨h, _⟩
    exact h

theorem matches_parse_posix_iff {r : Regex α} {s : List α} :
  r.Matches s ↔ ∃ v, r.parse s = some v ∧ POSIX r v := by
  simp [parse]
  rw [Matches.derivs_iff, ←nullable_iff_matches_nil]
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

theorem parse'_posix_iff (r : Regex α) (s : List α) (p : Parse r) :
  r.parse' s = some p ↔ p.flat = s ∧ POSIX' p := by
  constructor
  · intro h
    refine ⟨parse'_flat h, ?_⟩
    simp [parse'] at h
    rcases h with ⟨hn, h⟩
    rw [←h]
    exact injs'_posix mkeps'_posix
  · intro ⟨hv, h⟩
    subst hv
    rcases (matches_parse'_posix_iff.mp h.matches) with ⟨v', h', h''⟩
    rw [POSIX'.unique (parse'_flat h') h'' h] at h'
    exact h'
