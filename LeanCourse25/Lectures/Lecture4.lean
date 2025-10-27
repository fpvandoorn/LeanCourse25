import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic

open Real
noncomputable section
variable (a b c : ℝ)

/-
# Practical remarks

* Remember to disable the github copilot extension (if you haven't already)!
  You're not allowed to use AI for your homework.

* If you're building mathlib files on your computer, you need to get the mathlib cache first.
  The README explains how to do this. (short version: run `lake exe cache get`)

* The next homework assignment will be posted after class on GitHub.
  Due date: upload by 30.10., 10:00 on eCampus.
* As last time: the lecture is posted in advance of class,
  so you can open the file yourself during class.
* To get the latest version of this repository,
  follow the instructions in the README file.
-/


/- # Last time -/

/- Last time we saw how to deal with logic: if and only if, disjunction, exists and negation

Need to be precise about logical connectives, phrases like "to prove `A ∧ B` we have to prove
`A` and `B`." are awkward but necessary.

Overview of the most important connectives:

→   \to     if ... then ...           implication
∀   \all    for all                   universal quantification
∃   \ex     there exists              existential quantification
¬   \not    not                       negation
∧   \and    and                       conjunction
∨   \or     or                        disjunction
↔   \iff    ... if and only iff ...   biimplication
False       contradiction!            falsity
True        this is trivial           truth

... and how to use them:

            appearing as hypothesis `h`                appearing as goal
`A → B`     `have h' := h ha`, `apply h`               `intro ha`
`∀ x, P x`  `have h' := h x`, `apply h`, `specialize`  `intro x`

`A ∧ B`     `obtain ⟨ha, hb⟩ := h`, `h.1`, `h.2`       `constructor`
`A ∨ B`     `obtain := (ha | hb)`                      `left` or `right`
`∃ x. P x`  `obtain ⟨x, hx⟩ := h`                      `constructor` or `use x`

`False`     `contradiction`                            --
`True`      --                                         `trivial`

`¬ A`       `contradiction`                            `intro ha`
`A ↔ B`     `obtain ⟨h₁, h₂⟩ := h`                     `constructor`

We also saw the tactic `linarith`, for proving inequalities (and equalities)
that follow from linear combinations of assumptions.

-/

-- Let's remember how to work with negation.
example {p q : Prop} (h : p → q) : ¬q → ¬ p := by
  intro hq hp
  apply hq
  apply h hp
  done

/- # Today: classical reasoning, equality of functions; finding lemmas; working with orders -/


/- ## Logic (concluded): classical reasoning

We can use classical reasoning (with the law of the excluded middle)
using the following tactics.

* `by_contra h` start a proof by contradiction.
* `by_cases h : p` to start a proof by cases on statement `p`.
* `push_neg` to push negations inside quantifiers and connectives.
-/
example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  intro hp
  by_contra h'
  have := h h'
  apply h h' hp
  done

example (p r : Prop) (h1 : p → r) (h2 : ¬ p → r) : r := by
  by_cases hp : p
  · apply h1 hp
  · apply h2 hp
  done

example {α : Type*} {p : α → α → Prop} :
    ¬ (∃ x y, p x y) ↔ ∀ x y, ¬ p x y := by
  push_neg
  rfl
  done

/-
Note the difference between adding and removing a negation.
For the former (going from `hp : P` to `¬P`), we use `intro` in Lean.
For the latter (going from `hp : ¬P` to `P`),
we need to use `by_contra` to begin a proof by contradiction.
(In constructive mathematics, these are different.)
-/

/- The `contrapose` tactic starts a proof by contraposition -/
example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  contrapose
  assumption
  done

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  contrapose! -- same as contrapose; push_neg
  intro h
  linarith
  done

-- Final remark: the `use` tactic is compatible with constructive logic.


/-- The sequence `u` of real numbers converges to `l`.
`∀ ε > 0, ...` means `∀ ε, ε > 0 → ...` -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (u : ℕ → ℝ) (l : ℝ) : ¬ SequentialLimit u l ↔
    ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| ≥ ε := by
  unfold SequentialLimit
  push_neg
  rfl
  done

lemma sequentialLimit_unique (u : ℕ → ℝ) (l l' : ℝ) :
    SequentialLimit u l → SequentialLimit u l' → l = l' := by
  intro hl hl'
  by_contra H
  have h : 0 < |l - l'| := by sorry
  specialize hl (|l - l'| / 2) (by linarith)
  specialize hl' (|l - l'| / 2) (by linarith)
  obtain ⟨N, hN⟩ := hl
  obtain ⟨N', hN'⟩ := hl'
  let N₀ := max N N'
  have h1 : N₀ ≥ N := by sorry
  have h2 : N₀ ≥ N' := by sorry
  specialize hN N₀ h1
  specialize hN' N₀ h2
  have key : |l - l'| < |l - l'| := calc |l - l'|
      _ = |l - u N₀ + (u N₀ - l')| := by ring_nf
      _ ≤ |l - u N₀| + |u N₀ - l'| := by apply?
      _ = |u N₀ - l| + |u N₀ - l'| := by rw?
      _ < |l - l'| := by linarith
  linarith
  done


/- ## Proving two functions are equal

To prove that two functions `f g : α → β` are equal, you can prove that they are equal at every
point, using the `ext` tactic. `ext x` can prove that `f = g` if `f x = g x` for a new variable `x`.

-/

example {α β : Type*} {f g : α → β} (h : ∀ x, f x = g x): f = g := by
  ext y
  apply h y

-- `rfl` can prove an equality `f = f`,
example : (fun n ↦ n + 2 : ℤ → ℤ) = (fun n ↦ n + 2 : ℤ → ℤ) := rfl

-- but once two functions are not "obviously" equal, you need `ext` to prove it.
example : (fun n ↦ n + 2 : ℤ → ℤ) = (fun n ↦ n + 2 + 0 : ℤ → ℤ) := by
  -- rfl does not work
  ext n
  ring
  done

example : (fun n ↦ 2 * n : ℤ → ℤ) = (fun n ↦ n + n) := by
  ext k
  ring
  done

example : (fun (n : ℤ) ↦ 2 * n + 5) = (fun (n : ℤ) ↦ (n + 2) + (n + 6) - 3) := by
  ext k
  ring
  done


-- Let's take a more advanced example, where we need a little mathematics:
-- ZMod 5 is the set of residue classes modulo 5, with addition and multiplication of residue
-- classes defined by addition resp. multiplying their representatives.
#eval (3 : ZMod 5) + (4 : ZMod 5)
#eval (2 : ZMod 5) * (3 : ZMod 5)
#eval (4 : ZMod 5) * (5 : ZMod 5)

-- ZMod 5 with these operations is a ring (in fact, even a field as 5 is prime).


def f : ZMod 5 → ZMod 5 := fun x ↦ x ^ 5
def g : ZMod 5 → ZMod 5 := fun x ↦ x

#eval f 4
#eval g 4

-- Are f and g always equal? Yes! Let's prove it.
example : f = g := by
  ext x
  unfold f g
  -- There are only finitely many possible values for x: `fin_cases x` splits the goal into 5
  -- cases, one for each value.
  -- fin_cases x <;> rfl
  have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    -- The `simp` tactic can solve each of these.
    fin_cases x <;> simp
  obtain (h | h | h | h | h) := this <;> rw [h] <;> rfl
  done

















/-
We have seen two new tactics:
* if there are only finitely many values for `x` (because `x` has a type which has only finitely
  many elements), `fin_cases x` does a case analysis accordingly to the value of `x`
* the `simp` tactic is used to **simplify** expressions: in the setting above, this suffices to
  prove the goal. We will revisit this later.

* One more convenient shorthand: writing `<;>` between two tactics tells Lean
  "apply the following tactic to all goals at once"
-/

-- Let's do another such example.
-- Lean figures out the co-domain of the left hand side, and the type of the function
-- on the right hand side automatically.
example : (fun x ↦ x ^ 7 + 2 * x ^ 13 : ZMod 7 → _) = (fun x ↦ 3 * x) := by
  ext k
  fin_cases k <;> rfl
  done

-- Both of these examples hold for a deeper mathematical reason.
-- You will investigate this in the exercises.

/- # Finding Lemmas -/

/-
* Use tactics with a question mark to find a lemma.
  - `exact?` tries to apply a *single* lemma from the library to prove the current goal.
  - `apply?` tries to find all lemmas that can be used with `apply` to the current goal.
  - `rw?` tries to find all lemmas that can be used with `rw` on the current goal.
    `rw? at h` does the same at a hypothesis `h`
  - `rw??` finds lemmas that can be used with `rw` on the current goal, in an interactive way:
    After typing `rw??`, select an expression in the infoview,
    and shift-click on it. `rw??` will offer you several options, showing you how the expression
    looks afterwards. Choose one and click on it, and it automatically inserts the right `rw` call.
  - `have? using h1, h2` tries to find all facts that can be concluded from
    a single lemma using h1 and h2.
  - `simp?` simplifies the goal using `simp` and prints all used lemmas.

* Use `#leansearch "<query>."` to query theorems in natural language.
  Or use its website https://leansearch.net/

* Use `#loogle <query>` to query using syntactic searches, or its website
  https://loogle.lean-lang.org. The webpage also contains many search examples.

* Guess the name of the lemma
  - You can search lemmas in the API documentation:
    https://leanprover-community.github.io/mathlib4_docs/
  - When typing a name, a list of suggested completions automatically shows up
  - You can also press `ctrl-space` (or `cmd-space` on a Mac) to see the list of suggestions.
  - Pressing `ctrl-space` toggles the display of the documentation of the selected completion.
  - You can also press `ctrl-T` (or `cmd-T`) to search for a lemma name
    (choosing an option shows you where it is proven)

  Some naming conventions:
  - a theorem named `A_of_B_of_C` establishes something of the form `A`
    from hypotheses of the form `B` and `C`.
  - `A`, `B`, and `C` approximate the way we might read the statement out loud.
  - Example: a theorem showing `x + y ≤ ...` will probably start with `add_le`.
    After typing `add_le` the autocomplete will give you some helpful choices.

* You can browse Mathlib
If you ctrl-click on a definition or theorem in VS Code you will jump
to the file where the theorem is proven.
You can often find similar theorems nearby the theorem you searched for.
-/

example (a b x y : ℝ) (h : a < b) (h2 : x ≤ y) : a + exp x < b + exp y := by
  refine add_lt_add_of_lt_of_le h ?_ -- found by `apply?`
  -- another option: use apply
  -- have : exp x ≤ exp y := by
  --   exact exp_le_exp.mpr h2
  -- apply?
  exact exp_le_exp.mpr h2 -- found by `exact?`


/- In the following lemma, notice that `a`, `b`, `c`
are inside curly braces `{...}`.
This means that these arguments are *implicit*:
they don't have to be stated, but will be figured out by Lean automatically. -/

lemma cancel_addition {a b c : ℝ} (h : a + b = a + c) : b = c := by
  rw [add_left_cancel_iff] at h -- found by `rw? at h`
  assumption
  done

example {b c : ℝ} (h : 2 + b = 2 + c) : b = c := by
  exact cancel_addition h

/- {G : Type*} and [Group G] are both implicit arguments.
The difference will be discussed later. -/
#check inv_mul_cancel

-- Skipped during class.
example {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := by
  sorry
  done

-- Let's compare `rw?` and `rw??` on a more complicated example.
-- Note that I cannot select the expression `a * a⁻¹` on the right:
-- multiplication is left-associative, so a * b * c means (a * b) * c.
example {G : Type*} [Group G] (a : G) : a⁻¹ * a * a * a⁻¹ = 1 := by
  -- Let us try `rw?` first.
  -- rw?
  -- Now, we use `rw??`.
  rw [inv_mul_cancel a]
  rw [one_mul a]
  exact mul_inv_cancel a
  done

-- You can also use `rw??` at a hypothesis: simply select a local hypothesis in the infoview.
example {G : Type*} [Group G] {a b : G} (h : a⁻¹ * a * a * a⁻¹ = b) : b = 1 := by
  rw [inv_mul_cancel a] at h
  sorry -- Rest is exercise for you.
  done

lemma sequentialLimit_unique' (u : ℕ → ℝ) (l l' : ℝ) :
    SequentialLimit u l → SequentialLimit u l' → l = l' := by
  intro hl hl'
  by_contra H
  have : 0 < |l - l'| := by exact abs_sub_pos.mpr H
  specialize hl (|l - l'| / 2) (by linarith)
  specialize hl' (|l - l'| / 2) (by linarith)
  obtain ⟨N, hN⟩ := hl
  obtain ⟨N', hN'⟩ := hl'
  let N₀ := max N N'
  specialize hN N₀ (by exact Nat.le_max_left N N')
  specialize hN' N₀ (by exact Nat.le_max_right N N')
  have key : |l - l'| < |l - l'| := sorry
  linarith
  done


/- # Orders -/

section Real
variable {a b c d e x y z : ℝ}

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)


/- We can apply these lemmas manually, or use the `rfl`/`trans`/`calc` tactics. -/

example (x : ℝ) : x ≤ x := by exact le_refl x
example (x : ℝ) : x ≤ x := by apply le_refl
example (x : ℝ) : x ≤ x := by rfl

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  trans c
  · -- or: rwa [h₀]
    exact lt_of_eq_of_lt h₀ h₁
  · exact lt_of_le_of_lt h₂ h₃
  -- Another option: use a calc block
  -- calc a
  --   = b := h₀
  -- _ < c := h₁
  -- _ ≤ d := h₂
  -- _ < e := h₃

/- `linarith` can prove inequalities (and equalities)
  that follow from linear combinations of assumptions. -/

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
  done

example (x y z : ℝ) (hx : x ≤ 3 * y) (h2 : ¬ y > 2 * z)
    (h3 : x ≥ 6 * z) : x = 3 * y := by
  linarith
  done


/- mathlib has lemmas that all common operations are monotone. Here are a few examples. -/

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a)

-- Skipped during class.
example (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) : a * (b + 2) ≤ (a + c) * (b + 2) := by
  sorry
  done

/- `gcongr` is very convenient for monotonicity of functions. -/

example (h : a ≤ b) (h2 : b ≤ c) : exp a ≤ exp c := by
  gcongr
  -- or: exact le_trans a b c h h2
  trans b <;> assumption
  done

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  gcongr
  done

example (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) : a * (b + 2) ≤ (a + c) * (b + 2) := by
  gcongr
  -- `linarith` can solve this, but let's try a different option.
  -- To work with `gcongr`, it can be useful to insert additional `0` terms. Here's one example.
  calc
    a = a + 0 := by ring
    _ ≤ a + c := by gcongr

/-- END OF LECTURE HERE -/

/- Remark: for equalities, you should use `congr` instead of `gcongr` -/

example (h : a = b) : c - exp b = c - exp a := by
  sorry
  done

/- `grw` can be used to rewrite with more general relations than `=` and `↔`: for example,
inequalities or congruence relations -/

example {a b c d : ℤ} (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  sorry

#check 10 ≡ 2 [ZMOD 5]

example {a b n : ℤ} (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  sorry

example {a b c d n : ℤ} (h : a ≡ b [ZMOD n]) (h' : c ≡ d [ZMOD n]) :
    a ^ 2 * c ≡ b ^ 2 * d [ZMOD n] := by
  sorry

example {a b c : ℤ} (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) : a ∣ b ^ 2 * c := by
  sorry
  done

example (h₁ : a + e ≤ b + e) (h₂ : b < c) (h₃ : c ≤ d) : a + e ≤ d + e := by
  sorry

example (f g : ℝ → ℝ) (h : ∀ x : ℝ, f x ≤ g x) (h₂ : g a + g b ≤ 5) : f a + f b ≤ 5 := by
  sorry
