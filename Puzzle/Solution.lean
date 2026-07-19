import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Defs

-------------------DEFINITIONS------------------------------------------
abbrev ℤ₂ (n : ℕ) := Fin n → ZMod 2
notation "ℤ₂^" n : max => ℤ₂ n

def e (i : Fin n) : ℤ₂^n := Pi.single i 1

def SF (f : ℤ₂^n → Fin n) : Prop :=
    ∀ (b : ℤ₂^n) (k : Fin n), ∃ (i : Fin n), f (b + e i) = k

def HasStrategy (n : ℕ) : Prop := ∃ f : ℤ₂^n → Fin n, SF f

def δ (i j : Fin n) : ℕ := if i = j then 1 else 0
--------------------FUNCTION SHIFT IS INJECTIVE--------------------------
lemma fun_shift_surj (f : ℤ₂^n → Fin n) (h : SF f) (b : ℤ₂^n) :
    Function.Surjective (fun (i : Fin n) ↦ (f (b + e i) : Fin n)) := by
  unfold SF at h
  dsimp [Function.Surjective]
  exact h b

lemma fun_shift_inj (f : ℤ₂^n → Fin n) (h : SF f) (b : ℤ₂^n) :
    Function.Injective (fun i ↦ f (b + e i)) :=
  Finite.injective_iff_surjective.mpr (fun_shift_surj f h b)
---------------------FUNCTION SHIFT SUM--------------------------------
lemma fun_shift_sum_one (f : ℤ₂^n → Fin n) (h : SF f) (b : ℤ₂^n) (k : Fin n) :
    ∑ i , δ (f (b + e i)) k = 1 := by
  unfold SF at h
  obtain ⟨iₖ, hiₖ⟩ := h b k
  rw [Fintype.sum_eq_single iₖ]
  · unfold δ
    exact if_pos hiₖ
  · intro i h_neq
    unfold δ
    rw [← hiₖ]
    apply if_neg
    by_contra h_eq
    have h_eq := fun_shift_inj f h b h_eq
    exact h_neq h_eq

lemma fun_shift_sum_pow2 (f : ℤ₂^n → Fin n) (h : SF f) (k : Fin n) :
   ∑ b : ℤ₂^n, ∑ i : Fin n, δ (f (b + e i)) k = 2^n := by
  unfold SF at h
  have : ∀ b : ℤ₂^n, ∑ i : Fin n, δ (f (b + e i)) k = 1 := by
    intro b
    exact fun_shift_sum_one f h b k
  simp only [this]
  simp

lemma fun_shift_sum_rev (f : ℤ₂^n → Fin n) (k i : Fin n) :
    ∑ b, δ (f (b + e i)) k = ∑ b, δ (f b) k := by
  let g : ℤ₂^n → ℤ₂^n := fun b ↦ b + e i
  have bij_g : Function.Bijective g := by
    unfold g
    constructor
    · exact add_left_injective (e i)
    · exact add_right_surjective (e i)
  apply Fintype.sum_bijective g bij_g
  simp [g]
---------------------------MODUS PONENS-------------------------------
lemma strategy_pow2 (hn : 0 < n) (f : ℤ₂^n → Fin n) (h : SF f) :
    ∃ N, n * N = 2^n := by
  let k : Fin n := ⟨0, hn⟩
  have := fun_shift_sum_pow2 f h k
  rw [Finset.sum_comm] at this
  simp [fun_shift_sum_rev f k] at this
  use ∑ b, δ (f b) k

lemma mul_pow2 (h : ∃ N, n * N = 2 ^ n) : ∃ m, n = 2 ^ m := by
  obtain ⟨N, h_eq⟩ := h
  have h_eq : n ∣ 2 ^ n := Dvd.intro N h_eq
  have := (Nat.dvd_prime_pow Nat.prime_two).mp h_eq
  obtain ⟨m, hn, hm⟩ := this
  use m

theorem puzzle_mp (hn : 0 < n) (h : HasStrategy n) : ∃ m : ℕ, n = 2 ^ m := by
  unfold HasStrategy at h
  obtain ⟨f, hf⟩ := h
  exact mul_pow2 (strategy_pow2 hn f hf)
--------------------------MODUS PONENS REVERSE--------------------------
noncomputable def bij_Fin (m : ℕ) : Fin (2 ^ m) ≃ ℤ₂^m := by
  apply Fintype.equivOfCardEq
  simp

lemma sum_basis (i : Fin n) (f : Fin n → ℤ₂^m) : ∑ j, e i j • f j = f i := by
  unfold e
  rw [Fintype.sum_single_smul]
  simp

theorem puzzle_mpr (h : n = 2 ^ m) : HasStrategy n := by
  unfold HasStrategy
  unfold SF
  rw [h]
  let g := bij_Fin m
  use fun b ↦ g.symm (∑ j, b j • g j)
  dsimp
  intro b k
  simp only [add_smul, Finset.sum_add_distrib]
  let i := g.symm (g k - ∑ j, (b j • g j))
  use i
  rw [sum_basis i g]
  unfold i
  simp
------------------------------FINISH----------------------------------
theorem puzzle (hn : 0 < n) : HasStrategy n ↔ ∃ m, n = 2 ^ m := by
  constructor
  · exact puzzle_mp hn
  · intro ⟨m, hm⟩
    exact puzzle_mpr hm
