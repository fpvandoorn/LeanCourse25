import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Sets.Closeds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open BigOperators Function Set Filter Topology TopologicalSpace MeasureTheory
noncomputable section

/- # Today: Filters -/










/- # Limits -/


/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺`
* variations of the above with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior:
`f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

This gives `64` notions of limits.

When we prove that two limits compose: if
`f x` tends to `y₀` when `x` tends to `x₀` and
`g y` tends to `z₀` when `y` tends to `y₀` then
`(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.
This lemma has 512 variants.

Obviously we don't want to prove this 512 times.
Solution: use filters.










If `X` is a type, a filter `F : Filter X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following:
-/
section Filter

variable {X Y : Type*} (F : Filter X)

#check (F.sets : Set (Set X))
#check (F.univ_sets : univ ∈ F.sets)
-- A filter is closed under taking supersets.
#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)
-- A filter is closed under finite intersections.
#check (F.inter_sets : ∀ {U V},
  U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets)
end Filter






/-
Examples of filters:
-/

/- `(atTop : Filter ℕ)` is made of sets of `ℕ` containing
`{n | n ≥ N}` for some `N` -/
#check (atTop : Filter ℕ)

example {s : Set ℝ} : s ∈ atTop ↔
  ∃ N, ∀ n ≥ N, n ∈ s := by exact mem_atTop_sets

/- `𝓝 x`, made of neighborhoods of `x` in a topological space -/
#check (𝓝 3 : Filter ℝ)

/- `μ.ae` is made of sets whose complement has zero measure
with respect to a measure `μ`. -/
#check (ae volume : Filter (ℝ × ℝ × ℝ))

/-
It may be useful to think of a filter on a type `X`
as a generalized element of `Set X`.
* `atTop` is the "set of very large numbers"
* `𝓝 x₀` is the "set of points very close to `x₀`."
* For each `s : Set X` we have the so-called *principal filter*
  `𝓟 s` consisting of all sets that contain `s`.
-/


example {s t : Set ℝ} : t ∈ 𝓟 s ↔ s ⊆ t :=
  by exact mem_principal





/- Operations on filters -/

/- the *pushforward* of filters generalizes images of sets. -/
example {X Y : Type*} (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example {X Y : Type*} (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := by
  rfl

-- Let's check this really agrees with images of sets for principal filters.
example {X Y : Type*} (f : X → Y) {s : Set X} : (𝓟 s).map f = 𝓟 (f '' s) := by
  exact map_principal
  -- alternative proof: rw [mem_map, mem_principal, mem_principal, image_subset_iff]





-- Mapping filters is monotone: if l ≤ l', then l.map f ≤ l'.map f
#check Filter.map_mono

-- Mapping filters composes
#check Filter.map_map




/- the *pullback* of filters generalizes preimages -/
example {X Y : Type*} (f : X → Y) : Filter Y → Filter X :=
  Filter.comap f

-- This is again monotone and composes, but the composition is contravariant.
#check Filter.comap_mono
#check Filter.comap_comap

example {X Y : Type*} (f : X → Y) {s : Set Y} : (𝓟 s).comap f = 𝓟 (f ⁻¹' s) := by
  exact comap_principal


/- These form a *Galois connection* / adjunction -/
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  exact map_le_iff_le_comap

-- We can prove the composition law for `comap` from the Galois connection property
-- and `map_map`.
example {X Y Z : Type*} {f : Filter X} {m : Z → Y} {n : Y → X} :
    comap m (comap n f) = comap (n ∘ m) f := by
  apply le_antisymm
  · rw [← map_le_iff_le_comap]
    rw [← map_map]
    rw [map_le_iff_le_comap]
    rw [map_le_iff_le_comap]
  · rw [← map_le_iff_le_comap]
    rw [← map_le_iff_le_comap]
    rw [map_map]
    rw [map_le_iff_le_comap]





/- `Filter X` has an order that turns it into a complete lattice.
The order is reverse inclusion: -/
example {X : Type*} (F F' : Filter X) :
    F ≤ F' ↔ ∀ V : Set X, V ∈ F' → V ∈ F := by
  rfl

/- The principal filter `𝓟 : Set X → Filter X` monotone. -/
example {X : Type*} : Monotone (𝓟 : Set X → Filter X) := by
  exact monotone_principal


-- On principal filters, the supremum and infinum of filters correspond
-- to the union and intersection of their generating sets.
example {X : Type*} {s t : Set X} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) := by exact inf_principal

example {X : Type*} {s t : Set X} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) := by exact sup_principal

variable {X : Type*}
#check (⊤ : Filter X)
example : (⊤ : Filter X) = 𝓟 (univ : Set X) := Eq.symm principal_univ

example : (⊥ : Filter X) = 𝓟 (∅ : Set X) := by exact Eq.symm principal_empty
-- This bottom filter contains every subset of X.
example {s : Set X} : s ∈ (⊥ : Filter X) := by exact trivial

-- Note: Bourbaki assume that a filter is not the bottom filter.
-- Mathlib chooses a different definition: the bottom filter is a filter,
-- which makes the type of filters on `X` into a complete lattice.

-- The definition `NeBot` describes that a filter is not the bottom filter.
#check NeBot

example [TopologicalSpace X] {x : X} : NeBot (𝓝 x) := by exact nhds_neBot


/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

-- Would the definition be different if we used the comap instead?
-- No, because of the Galois adjunction property.
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    map f F ≤ G ↔ F ≤ comap f G := by
  exact map_le_iff_le_comap

#check Tendsto

lemma Tendsto_iff {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := by
  -- This is true by `rfl`; let us expand the definition by hand.
  rw [Tendsto]
  simp only [(· ≤ ·)]
  simp_rw [mem_map] -- or: simp only [mem_map]
  -- note that `rw` does not work because it cannot rewrite inside a ∀ quantifier


/- A sequence `u` converges to `x` -/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = y₀⁺` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) (𝓝[≥] y₀)

/- `\lim_{x → ∞} f x = y` -/
example (f : ℝ → ℝ) (y : ℝ) : Tendsto f atTop (𝓝 y) := sorry

/- `\lim_{x → ∞} f x = ∞` -/
example (f : ℝ → ℝ) : Tendsto f atTop atTop := sorry

/- `\lim_{x → -∞} f x = ∞` -/
example (f : ℝ → ℝ) : Tendsto f atBot atTop := sorry

/- Now the following states all possible composition lemmas all at
once! -/
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by
  rw [Tendsto] at hf hg ⊢
  calc
    map (g ∘ f) F
    _ = map g (map f F) := by rw [map_map]
    _ ≤ map g G := by
      gcongr
      -- or: apply map_mono; exact hf
    _ ≤ H := hg










/-
Filters also allow us to reason about things that are
"eventually true". If `F : Filter X` and `P : X → Prop` then
`∀ᶠ n in F, P n` means that `P n` is eventually true for `n` in `F`.
It is defined to be `{ x | P x } ∈ F`.

The following example shows that if `P n` and `Q n` hold for
sufficiently large `n`, then so does `P n ∧ Q n`.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

-- This example is quite simple: in more complicated examples, it's useful to separate the
-- bookkeeping from the mathematical content: this is what the `filter_upwards` tactic is good for.
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  -- `filter_upwards [hP, hQ]` converts your goal to `∀ n, P n → Q n → (P n ∧ Q n)`
  filter_upwards [hP, hQ]
  -- Now, we are out of "filter land" and only need to prove some basic logic.
  intro n hpn hqn
  tauto -- solves elementary logic problems
  -- or: `constructor <;> assumption`

/- If `P n` holds for sufficiently large `n`, then clearly does `P n ∨ Q n`:
we can use `Filter.Eventually.mono` to express this: `P n` implies `P n ∨ Q n` -/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (_hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∨ Q n := by
  sorry

/- If `P n` implies `Q n` and `P n` holds for sufficiently large `n`, then so does `Q n`:
this is another instance of `Filter.Eventually.mono` -/
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ n, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  --apply hP.mono
  --apply hPQ
  -- let's use filter_upwards now
  filter_upwards [hP] using hPQ

/- Let's make that a bit more complicated: assume if `P n` implies `Q n` for n sufficiently large
and `P n` holds for sufficiently large `n` --- then so does `Q n`. -/
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ᶠ n in atTop, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  -- filter_upwards [hP, hPQ]
  -- intro n hp hpq
  -- exact hpq hp
  -- short version, equivalent to the above three lines
  filter_upwards [hP, hPQ] with n hp hpq using hpq hp

example (P Q R S : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, R n) (hS : ∀ᶠ n in atTop, S n) : ∀ᶠ n in atTop, P n ∧ Q n ∧ R n ∧ S n := by
  -- tactic proof: apply hP.and (hQ.and (hR.and hS))

  filter_upwards [hP, hQ, hR, hS]
  tauto

/- END OF LECTURE -/

-- We can state our definition of tendsto using the language of Filter.Eventually.
example (u : ℕ → ℝ) (x : ℝ) : MyTendsto u atTop (𝓝 x) ↔ ∀ s ∈ 𝓝 x, ∀ᶠ n in atTop, u n ∈ s := by
  sorry
