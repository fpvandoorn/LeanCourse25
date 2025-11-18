import Mathlib.Analysis.Complex.Exponential

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
open Real Function Set

/-

* An advertisement: for a current event by the *Fachschaft* you may find interesting:

**Equity in math-an event for men**
The event will take place on 17 November from 16:00 to 18:00 in the Lipschitzsaal.
The Gleichstellungsreferat of the Fachschaft Mathematik warmly invites you to this event,
where we will discuss male perspectives on gender equality.
The program will include a talk on the topic, a panel discussion with professors and students, and
the opportunity to chat over drinks and enjoy free cookies afterwards.
You can find more information on our website at fsmath.uni-bonn.de.
Of course, everyone is welcome to join — we look forward to seeing you there 🙂


* Hand in the solutions to the exercises below. Deadline: **Thursday**, 20.11.2025 at 10.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

-- Remember the definition Point from last week's assignment: let's parametrise this by a type.
@[ext]
structure Point (α : Type*) where
  x : α
  y : α
  z : α

-- Let's connect this to ℝ³. Here is to define a point in a triple:
-- you can use matching, just like you would for an inductive type.
example {x y z : ℝ} : Fin 3 → ℝ := fun
  | 0 => x
  | 1 => y
  | 2 => z

-- Define an equivalence from Fin 2 × Fin 3 to Fin 6.
example : Fin 3 × Fin 2 ≃ Fin 6 := sorry

-- Now prove that Point α and α³ are equivalent.
-- In particular, `Point` from last week and `ℝ³` are equivalent.
example {α : Type*} : (Fin 3 → α) ≃ Point α where
  toFun := fun f ↦ ⟨f 0, f 2, f 1⟩
  invFun P := fun
    | 0 => P.x
    | 1 => P.z
    | 2 => P.y
  left_inv := by sorry
  right_inv := by sorry

section

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by
  sorry
  done

end

section

-- In the lecture, we also saw injectivity and bijectivity of functions.
-- There is another variant, "bijectivity on a set":
def BijectiveOn {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (f '' s ⊆ t) ∧ InjOn f s ∧ SurjOn f s t

-- There is a curious fact about infinite types: they are bijective to a proper subset.
-- Let us explore this theme in the following exercises.

example : ∃ f : ℕ → ℕ, BijectiveOn f univ (univ \ {0}) := by
  sorry

example {α : Type*} [Infinite α] {a : α} : ∃ f : α → α, BijectiveOn f (univ \ {a}) univ := by
  -- Hint: a useful first step is "there exists an injective map ℕ → α".
  -- Use loogle or exact? to find this.
  sorry

-- In particular, an infinite type is bijective to a proper subtype.
-- If you like a little *challenge*, prove the converse.
-- This is a bit harder; you want to write down a careful mathematical proof first
-- and use loogle to re-use existing results from mathlib.
example {α : Type*} {s : Set α} (hs : s ≠ univ) {f : α → α} (hf : BijectiveOn f s univ) :
    Infinite α := by
  sorry

end



/-! # Exercises to hand-in. -/

-- There are only two exercises to hand in this week. In the remaining time, work on your first
-- project about formal conjectures.

section choice

/-- This exercise is about a subtle detail regarding the axiom of choice: while you know there
is a global choice function, it is not given by one "computation rule".
The following exercise makes this precise: prove it.

Remember that Lean has proof irrelevance: any two proofs of a given proposition are equal.
-/

example (choiceFunction : ∀ (α : Type) (p : α → Prop) (_h : ∃ x, p x), α)
    (h : ∀ (α : Type) (p : α → Prop) (x : α) (hx : p x),
      choiceFunction α p ⟨x, hx⟩ = x) :
    False := by
  -- Wir nehmen α = Bool und ein triviales Prädikat.
  let p : Bool → Prop := fun _ => True
  have ht : p true := trivial
  have hf : p false := trivial

  -- Nach der gegebenen "Rechenregel":
  have ht_eq : choiceFunction Bool p ⟨true, ht⟩ = true :=
    h Bool p true ht
  have hf_eq : choiceFunction Bool p ⟨false, hf⟩ = false :=
    h Bool p false hf

  -- In Prop (also auch für ∃ b, p b) gilt Beweis-Irrelevanz:
  have hexists_eq : (⟨true, ht⟩ : ∃ b, p b) = ⟨false, hf⟩ :=
    Subsingleton.elim _ _

  -- Also müssen auch die Werte der choiceFunction gleich sein:
  have hchoice_eq :
      choiceFunction Bool p ⟨true, ht⟩ =
        choiceFunction Bool p ⟨false, hf⟩ :=
    congrArg (choiceFunction Bool p) hexists_eq

  -- Daraus folgt true = false, Widerspruch.
  have : true = false := by
    calc
      true = choiceFunction Bool p ⟨true, ht⟩ := ht_eq.symm
      _    = choiceFunction Bool p ⟨false, hf⟩ := hchoice_eq
      _    = false := hf_eq

  exact (Bool.eq_not_self true).mp this

end choice

section cardinality

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] Finset.card_powerset
#check Finset.induction
#check insert


example (α : Type*) [DecidableEq α] (s : Finset α) (a : α) : insert a s = {a} ∪ s := by rfl


lemma finset_card_powerset (α : Type*) [DecidableEq α] (s : Finset α) :
    Finset.card (Finset.powerset s) = 2 ^ Finset.card s := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      have hsplit:
        Finset.powerset (insert a s)
          =  Finset.powerset s ∪
            (Finset.powerset s).image (fun t => insert a t ) := by
        exact Finset.powerset_insert s a

      have hdisj:
        Disjoint (Finset.powerset s ) ((Finset.powerset s).image (fun t => insert a t )) := by

          -- Use the characterization of disjointness for Finsets:
          -- A and B are disjoint if for every element t,
          -- t ∈ A → t ∈ B → False.
        refine Finset.disjoint_left.mpr ?_

        -- Introduce:
        -- t  = a candidate subset
        -- ht  : t ∈ powerset s
        -- ht' : t ∈ image (insert a) (powerset s)
        intro t ht ht'

        -- From membership in the image, we obtain:
        --  t = insert a u for some u ∈ powerset s.
        rcases Finset.mem_image.mp ht' with ⟨u, hu, rfl⟩

        -- From ht : t ∈ powerset s and t = insert a u,
        -- we get the subset condition:
        --   insert a u ⊆ s.
        have hsubset : insert a u ⊆ s := Finset.mem_powerset.mp ht

        -- But a is always contained in insert a u.
        have ha_in : a ∈ insert a u :=  Finset.mem_insert_self a u

        -- Therefore a ∈ s.
        have this: a ∈ s := hsubset ha_in

        -- But this contradicts the induction hypothesis ‘ha : a ∉ s’.
        exact ha this

      have hinj:
          ∀ t u: Finset α,
          t ∈ Finset.powerset s →
          u ∈ Finset.powerset s →
          insert a t = insert a u → t = u := by
            intro t u ht hu h
            refine Finset.ext_iff.mpr ?_

            -- From t,u ∈ powerset s we know: t ⊆ s and u ⊆ s
            have ht_ss : t ⊆ s := Finset.mem_powerset.mp ht
            have hu_ss : u ⊆ s := Finset.mem_powerset.mp hu

            -- Since a ∉ s, a ∉ t and a ∉ u
            have ha_t : a ∉ t := fun h_mem => ha (ht_ss h_mem)
            have ha_u : a ∉ u := fun h_mem => ha (hu_ss h_mem)

            -- Remove a from both sides of insert a t = insert a u
            -- Lean has: Finset.erase_insert ha_t : erase a (insert a t) = t
            --           Finset.erase_insert ha_u : erase a (insert a u) = u
            have h₁:= congrArg (Finset.erase · a) h
          -- erase-insert identities
            have h₂ : (insert a t).erase a = t :=
              Finset.erase_insert ha_t
            have h₃ : (insert a u).erase a = u :=
              Finset.erase_insert ha_u

            -- chain equalities to get t = u
            have htu : t = u := by
              calc
                t = (insert a t).erase a := h₂.symm
                _ = (insert a u).erase a := h₁
                _ = u := h₃
            simp[htu]


      -- Now compute cardinalities:
      -- |powerset (insert a s)| = |powerset s| + |image|
      -- and |image| = |powerset s|
 -- cardinality of the image: same as cardinality of powerset s
      have hcard_image :
        Finset.card ((Finset.powerset s).image (fun t => insert a t)) =
          Finset.card (Finset.powerset s) := by
        -- card_image_iff lets us use our injectivity lemma
        apply Finset.card_image_iff.mpr
        intro t u ht hu h
        exact hinj t ht u hu h

      -- cardinality of the union from the split decomposition
      have hcard_union :
        Finset.card (Finset.powerset (insert a s)) =
          Finset.card (Finset.powerset s)
          + Finset.card ((Finset.powerset s).image (fun t => insert a t)) := by
        simp[hsplit]
        exact Finset.card_union_of_disjoint hdisj

      -- Now compute cardinalities:
      -- |powerset (insert a s)| = |powerset s| + |image|
      -- and |image| = |powerset s|
      calc
        Finset.card (Finset.powerset (insert a s))
            = Finset.card (Finset.powerset s)
              + Finset.card ((Finset.powerset s).image (fun t => insert a t)) := hcard_union
        _   = Finset.card (Finset.powerset s)
              + Finset.card (Finset.powerset s) := by
                simp [hcard_image]
        _   = 2 * Finset.card (Finset.powerset s) := by
                simp [two_mul]
        _   = 2 * 2 ^ Finset.card s := by
                simp [ih]
        _   = 2 ^ Finset.card s * 2 := by
                ac_rfl
        _   = 2 ^ (Finset.card s + 1) := by
                simp [pow_succ, Nat.mul_comm]
        _   = 2 ^ Finset.card (insert a s) := by
                -- card (insert a s) = card s + 1 since a ∉ s
                refine (Nat.pow_right_inj ?_).mpr ?_
                linarith
                exact Eq.symm (Finset.card_insert_of_notMem ha)

end cardinality
