/-
Authors: Lean-Cluj Summer School 2026
-/

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs

-------------------DEFINITIONS------------------------------------------
abbrev Z2 (n : ℕ) := Fin n → ZMod 2
notation "ℤ₂^" n : max => Z2 n

def e (i : Fin n) : ℤ₂^n := Pi.single i 1

def SF (f : ℤ₂^n → Fin n) : Prop :=
    ∀ (b : ℤ₂^n) (k : Fin n), ∃ (i : Fin n), f (b + e i) = k

def HasStrategy (n : ℕ) : Prop := ∃ f : ℤ₂^n → Fin n, SF f

def δ (i j : Fin n) : ℕ := if i = j then 1 else 0
--------------------FUNCTION SHIFT IS INJECTIVE--------------------------
lemma fun_shift_surj (f : ℤ₂^n → Fin n) (h: SF f) (b: ℤ₂^n ):
            Function.Surjective (fun i => f (b + e i)) := by -- lemma 4.1
    unfold Function.Surjective
    dsimp
    intro k
    exact Set.mem_range.mp (h b k)

lemma fun_shift_inj (f : ℤ₂^n → Fin n) (h: SF f) (b: ℤ₂^n ):
            Function.Injective (fun i => f (b + e i)) := by -- lemma 4.2
    have hIS := (Finite.injective_iff_surjective (f := fun i => f (b + e i))).mpr
    have hS := fun_shift_surj f h b
    exact (hIS hS)

---------------------FUNCTION SHIFT SUM--------------------------------
lemma fun_shift_sum_one (f : ℤ₂^n → Fin n) (h: SF f) (k: Fin n) (b:ℤ₂^n) : -- lemma 5.1
            1 = ∑ i, δ (f (b + e i)) k := by
    unfold SF at h
    have t := h b k
    obtain ⟨ik, hf⟩ := t
    rw [Fintype.sum_eq_single ik]
    · unfold δ
      symm
      apply if_pos
      exact hf
    · intro x hx
      have hi := fun_shift_inj f h b
      unfold δ
      apply if_neg
      have hI := fun a => hx (hi a)
      exact ne_of_ne_of_eq hI hf



lemma fun_shift_sum_pow2 (f : ℤ₂^n -> Fin n) (h : SF f) (k : Fin n) :
  ∑ b, ∑ i, δ (f (b + e i)) k = 2 ^ n := by
    have hl : ∀ b : ℤ₂^n, ∑ i, δ (f (b + e i)) k = 1 := by
        intro b
        exact (fun_shift_sum_one f h k b).symm
    simp [hl]

lemma fun_shift_sum_rev (f : ℤ₂^n → Fin n) (k i : Fin n) : ∑ b, δ (f (b + e i)) k = ∑ b, δ (f b) k :=
  by
    let g (b: ℤ₂^n): ℤ₂^n := b + e i
    have h : Function.Bijective g :=
      by
        constructor
        · unfold Function.Injective
          apply add_left_injective
        · unfold Function.Surjective
          apply add_right_surjective
    --exact
      --Function.Bijective.finsetSum g h (fun x ↦ δ (f (x + e i)) k) (fun x ↦ δ (f x) k)
        --(congrFun rfl)
    apply Fintype.sum_bijective g h
    simp [g]
---------------------------MODUS PONENS-------------------------------
lemma strategy_pow2 (hn: 0 < n) (f : ℤ₂^n -> Fin n) (hf: SF f) :
    ∃ N, n * N = 2 ^ n := by
    let k : Fin n := ⟨0 , hn⟩
    have h: ∑ b, ∑ i, δ (f (b + e i)) k = 2^n := fun_shift_sum_pow2 f hf k
    rw [Finset.sum_comm] at h
    have h1: ∀ i , ∑ b, δ (f (b + e i)) k = ∑ b, δ (f b) k := fun_shift_sum_rev f k
    simp [h1] at h
    use ∑ b, δ (f b) k


lemma mul_pow2 (h: ∃ N, n * N = 2 ^ n): ∃ m, n = 2 ^ m := by
    obtain ⟨N, hN⟩ := h
    have hdvd : n ∣ 2 ^ n := Dvd.intro N hN
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩

theorem puzzle_mp (hn: 0 < n) (hs: HasStrategy n) : ∃ m : ℕ, n = 2 ^ m := by
    obtain ⟨f, hf⟩ := hs
    have h1 := strategy_pow2 hn f hf
    have h2 := mul_pow2 h1
    exact h2
--------------------------MODUS PONENS REVERSE--------------------------
noncomputable def bij_Fin : Fin (2 ^ m) ≃ ℤ₂^m :=
by
  apply Fintype.equivOfCardEq
  simp?

lemma sum_basis ( i : Fin n) (f : Fin n → ℤ₂^m) : ∑ j, (e i j) • (f j) = f i :=
by
  unfold e
  simp [Fintype.sum_single_smul]

theorem puzzle_mpr (h : ∃ m, n = 2 ^ m) : HasStrategy n := by
  obtain ⟨m, h⟩ := h
  rw[HasStrategy]
  dsimp [SF]
  let g := @bij_Fin m
  let g_inv := g.symm
  let f := (λb : ℤ₂^(2^m) => g_inv (∑ j, (b j) • (g j)))
  rw[h]
  use f
  intro b k
  let i := g_inv (g k - (∑ j, (b j) • (g j)))
  unfold f
  use i
  unfold i
  simp [Finset.sum_add_distrib, add_smul]
  rw [sum_basis]
  unfold g_inv
  simp
------------------------------FINISH----------------------------------
theorem puzzle (n : ℕ) (h : n > 0) : HasStrategy n ↔ ∃ m : ℕ, n = 2 ^ m := by
    constructor
    ·   intro hs
        apply puzzle_mp h hs
    ·   apply puzzle_mpr
