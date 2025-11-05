import Mathlib.Analysis.Complex.Exponential

import Mathlib
open Real Function Set Nat

/-

* Hand in the solutions to the exercises below. Deadline: **Monday**, 10.11.2025 at **19:00**.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

section calculations

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by
  sorry
  done

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by
  sorry
  done

end calculations

section Min
variable (a b c d : ℝ)

/- The following theorems characterize `min`.
Let's use this characterization of it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by
  sorry
  done

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by
  sorry
  done

-- Prove the following exercise. You can use mathlib tactics now.
lemma exercise_min : min (min a (min (min b c) c)) d = min (min a (min d b)) c := by
  sorry
  done

end Min

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by
  sorry
  done


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
example (p : Prop) : p ∨ ¬ p := by
  sorry
  done

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (132 + 32 * 3, (x + y) ^ 2) = (228, x ^ 2 + 2 * x * y + y ^ 2) := by
  sorry
  done

/- Prove a version of the axiom of choice Lean's `Classical.choose`.

Note: this might be a bit harder; you will probably find `Classical.choose` and
`Classical.choose_spec` useful. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by
  sorry
  done

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by
  sorry
  done

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by
  sorry
  done

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry
  done

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by
  sorry
  done

end Set

section casts

/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by
  sorry
  done

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by
  sorry
  done

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by
  sorry
  done

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by
  sorry
  done

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by
  sorry
  done

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by
  sorry
  done

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by
  sorry
  done

end casts

/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i ∈ Finset.range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by
  sorry
  done

example (n : ℕ) : ∑ i ∈ Finset.range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by
  sorry
  done

example (n : ℕ) : 6 * ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  sorry
  done

/-! # Exercises to hand-in. -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  sorry
  done

/- Prove this without using lemmas from Mathlib. -/
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry
  done

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  sorry
  done

section

-- In class, we saw that Lean does not accept definitions like this:
-- def wrong : ℕ → ℕ
--  | n => 1 + wrong (n + 1)

-- In this case, you can actually derive a contradiction from a function with this property.
-- Do so in the following exercise.
-- (If you'd like a mathematical hint, scroll to the bottom of this file.)
example (f : ℕ → ℕ) (h : ∀ n : ℕ, f n = 1 + f (n + 1)) : False := by
  sorry
  done

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ 3) = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 := by
  sorry
  done

end

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  sorry
  done

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  sorry
  done

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  sorry
  done

end Surjectivity

-- Hint for the exercise `contradictory_definition`:
-- use the hypothesis to study `f 0`: can you relate it to `f 1`, `f 2`, etc.?
-- Perhaps you can formulate a hypothesis and prove it by induction.
