/-
Copyright (c) 2026 firesh.
Released under Apache 2.0; see LICENSE.
-/

import Mathlib

/-!
# JSP-000301 / Erdős Problem 365

This file formalizes Solomon W. Golomb's counterexample to the claim that, if
two consecutive positive integers are powerful, at least one is a square.

The counterexample is

* `12167 = 23³`, and
* `12168 = 2³ · 3² · 13²`.

Both numbers are powerful, while both lie strictly between `110²` and `111²`.
-/

namespace Jsp000301

/-- A natural number is powerful when the square of each of its prime divisors
also divides it.  The finite `primeFactors` formulation makes concrete
certificates executable. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ^ 2 ∣ n

/-- The finite definition agrees with the standard quantified definition for
positive natural numbers. -/
theorem powerful_iff {n : ℕ} (hn : n ≠ 0) :
    Powerful n ↔ ∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n := by
  constructor
  · intro h p hp hd
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)
  · intro h p hp
    exact h p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- A natural number is a perfect square. -/
def PerfectSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, n = k ^ 2

theorem factorization_12167 : 12167 = 23 ^ 3 := by norm_num

theorem factorization_12168 : 12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by norm_num

/-- `12167 = 23³` is powerful. -/
theorem powerful_12167 : Powerful 12167 := by
  have hpf : (12167 : ℕ).primeFactors = {23} := by decide +kernel
  intro p hp
  rw [hpf] at hp
  simp only [Finset.mem_singleton] at hp
  subst p
  norm_num

/-- `12168 = 2³·3²·13²` is powerful. -/
theorem powerful_12168 : Powerful 12168 := by
  have hpf : (12168 : ℕ).primeFactors = {2, 3, 13} := by decide +kernel
  intro p hp
  rw [hpf] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

/-- Every square at most `12167` has root at most `110`. -/
private theorem root_le_110_of_square_le_12167 {k : ℕ} (h : k ^ 2 ≤ 12167) :
    k ≤ 110 := by
  by_contra hk
  have h111 : 111 ≤ k := by omega
  nlinarith

/-- `12167` lies strictly between two consecutive squares. -/
theorem not_square_12167 : ¬ PerfectSquare 12167 := by
  rintro ⟨k, hk⟩
  have hle : k ≤ 110 := root_le_110_of_square_le_12167 (by omega)
  nlinarith

/-- Every square at most `12168` has root at most `110`. -/
private theorem root_le_110_of_square_le_12168 {k : ℕ} (h : k ^ 2 ≤ 12168) :
    k ≤ 110 := by
  by_contra hk
  have h111 : 111 ≤ k := by omega
  nlinarith

/-- `12168` also lies strictly between the same consecutive squares. -/
theorem not_square_12168 : ¬ PerfectSquare 12168 := by
  rintro ⟨k, hk⟩
  have hle : k ≤ 110 := root_le_110_of_square_le_12168 (by omega)
  nlinarith

/-- The proposed assertion, stated independently of the counterexample. -/
def ConsecutivePowerfulSquareClaim : Prop :=
  ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
    PerfectSquare n ∨ PerfectSquare (n + 1)

/-- **JSP-000301 / Erdős 365.** Golomb's consecutive pair refutes the
assertion that one of two consecutive positive powerful integers must be a
perfect square. -/
theorem jsp000301 : ¬ ConsecutivePowerfulSquareClaim := by
  intro h
  have hsquare := h 12167 (by norm_num) powerful_12167 (by norm_num [powerful_12168])
  rcases hsquare with hleft | hright
  · exact not_square_12167 hleft
  · norm_num at hright ⊢
    exact not_square_12168 hright

/-- The same result as an explicit positive consecutive counterexample. -/
theorem golomb_counterexample :
    ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
      ¬ PerfectSquare n ∧ ¬ PerfectSquare (n + 1) := by
  refine ⟨12167, by norm_num, powerful_12167, ?_, not_square_12167, ?_⟩
  · norm_num [powerful_12168]
  · norm_num [not_square_12168]

end Jsp000301
