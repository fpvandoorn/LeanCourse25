import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Sets.Closeds

open BigOperators Function Real Set Filter Topology TopologicalSpace MeasureTheory
noncomputable section

/- ## Last time: filters

* filters are generalized sets, and can capture notions
  like "very large numbers" (`atTop`) or
  "points close to `x`" (`𝓝 x`).
* pushforward (`map`) and pullback (`comap`) of a filter; these form a Galois connection
* on the principal filter, these correspond to image and preimage

* We can define limits using `Filter.tendsto`
* `∀ᶠ x in F, P x` states that `x` holds eventually in `F`.
* the `filter_upwards` tactic allows converting from "filter world" to "logic world"

-/

#check Tendsto

-- We can state our definition of tendsto using the language of `Filter.Eventually`.
example (u : ℕ → ℝ) (x : ℝ) : Tendsto u atTop (𝓝 x) ↔ ∀ s ∈ 𝓝 x, ∀ᶠ n in atTop, u n ∈ s := by
  simp only [Tendsto]
  refine ⟨?_, ?_⟩ -- or: `constructor`
  · intro h s hs
    specialize h hs
    rw [mem_map, mem_atTop_sets, ← eventually_atTop] at h
    filter_upwards [h] with a ha using ha
    -- or:
    --apply h.mono
    --intro x hx
    --exact hx
  · intro h s hs
    rw [mem_map, mem_atTop_sets, ← eventually_atTop]
    exact h s hs
    done


/- ## Today: topology -/


section Topology

/- Let's look at the definition of topological space. -/

universe u v w
variable {X : Type u} [TopologicalSpace X]
  {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]


example {ι : Type*} (s : ι → Set X) :
    interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) := by
  intro x hx
  rw [mem_iInter]
  intro i
  apply interior_mono _ hx
  apply iInter_subset_of_subset i subset_rfl


/- A map between topological spaces is continuous if the
preimages of open sets are open. -/
example {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

/- It is equivalent to saying that for any `x₀` the function
value `f x` tends to `f x₀` whenever `x` tends to `x₀`. -/
example {f : X → Y} :
    Continuous f ↔ ∀ x₀, Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact continuous_iff_continuousAt

/- By definition, the right-hand side states that `f` is
continuous at `x₀`. -/
example {f : X → Y} {x₀ : X} :
    ContinuousAt f x₀ ↔ Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  rfl

-- Stated in terms of the order on filters, this is equivalent to the following.
example {f : X → Y} {x : X} :
    ContinuousAt f x ↔ (𝓝 x).map f ≤ 𝓝 (f x) := by
  rfl


-- Let us use this to prove that the composition of continuous functions is continuous.
example {f : X → Y} {g : Y → Z} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g (f x)) :
    ContinuousAt (g ∘ f) x := by
  rw [ContinuousAt] at hf hg ⊢
  apply Tendsto.comp hg
  apply hf

-- We already proved this in the first class --- but note how this follows immediately from
-- the composition lemma that we proved for filters!

-- In particular, the composition of continuous functions is continuous.
example {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  rw [continuous_iff_continuousAt] at hf hg ⊢
  intro x
  exact (hg (f x)).comp (hf x)




/- Superficially, it may seem that `Tendsto u atTop (𝓝 x₀)` is stronger
than the familiar notion of convergence:
we ask that every neighborhood of `x₀` has a preimage belonging to `atTop`,
whereas the usual definition only requires this
for the standard neighborhoods `Ioo (x₀ - ε) (x₀ + ε)`.
The key is that, by definition, every neighborhood contains such a standard one.
This observation leads to the notion of a filter basis. -/

/- Let `F` be a filter on `X` and `s : ι → Set X` a family of sets on `X`.
We say `s` is a basis for `F` if for every set `U`, we have `U ∈ F`
if and only if it contains some `s i`.
-/
def HasBasis' {ι : Type*} {F : Filter X} {s : ι → Set X} : Prop :=
  ∀ U : Set X, U ∈ F ↔ ∃ i, s i ⊆ U

/- Mathlib's definition is slightly more flexible: it also considers a predicate
on `ι` that selects only some of the values `i` in the indexing type. -/
#check Filter.HasBasis

/- In the case of `𝓝 x₀`, we want `ι` to be `ℝ`, we write `ε` for `i`,
and the predicate should select the positive values of `ε`.

So, this is how to state that the sets `Ioo (x₀ - ε) (x₀ + ε)` form a basis
for the neighborhood topology on `ℝ`: -/
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  sorry

-- The `atTop` filter also has a nice basis.
#check Filter.atTop_basis

-- We can reformulate a statement `Tendsto f F G` given bases for F and G.
#check Filter.HasBasis.tendsto_iff

-- This gives another proof that convergence w.r.t. filters
-- agrees with the notion we know from an analysis course.
example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp
























/- ## Proving "boring" continuity goals

If we want to prove that the composition of two complicated continuous functions is continuous,
we can use lemmas of composition, addition, multiplication etc. of continuous functions.
-/

example : Continuous (fun x ↦ 2 + x * Real.sin x) := by
  apply Continuous.add
  · apply continuous_const
  apply Continuous.mul
  apply continuous_id
  apply continuous_sin
  done

-- Note: continuous_sin says "the sin function is continuous".
-- Continuous.sin would say "assume f is continuous, then sin ∘ f is continuous".
-- #check Continuous.sin

/- Manually applying them gets kind of tedious, however: is there a tactic to help us?
Yes: the `fun_prop` tactic is great for proving goals of the form "this function is the
composition of continuous functions, therefore continuous" -/

example : Continuous (fun x ↦ 2 + x * Real.sin x) := by
  show_term fun_prop

example {f : ℝ → ℝ} (hf : Continuous f) : ContinuousAt (fun x ↦ 2 + f x * Real.sin x) 2 := by
  fun_prop

-- `fun_prop` know about measurability, differentiability etc. and the relations between them
-- (e.g., differentiable functions are continuous, continuous functions are measurable, etc.)
-- We will encounter this again when discussing calculus and measure theory.







/- ## Topological spaces, continued -/


-- Let's look at the neighbourhood filter in more detail

/- Neighborhoods are characterized by the following lemma. -/
example {x : X} {s : Set X} :
    s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  by exact mem_nhds_iff

example {x : X} {s : Set X} (h : s ∈ 𝓝 x) : x ∈ s := by
  exact mem_of_mem_nhds h

-- An open set containing x is a neighbourhood of x (an *open neighbourhood*).
-- Note: many textbook proofs use open neighbourhoods, when in fact any neighbourhood may suffice.
-- Formalisation can teach you something about mathematics also.
example {x : X} (s : Set X) (hs : IsOpen s) (hx : x ∈ s) : s ∈ 𝓝 x := by
  apply hs.mem_nhds hx

-- You should really think of the neighbourhood filter as a generalised set corresponding to
-- "the intersection of all open sets containing x".
-- As a set, this intersection of all open subsets containing x is usually not useful:
-- in the real numbers, for example, it is just `{x}`, which is far from being open.
example {x : ℝ} : ⋂ i ∈ {s : Set ℝ | IsOpen s ∧ x ∈ s }, i = {x} := by
  -- apply?
  sorry




-- A homeomorphism between topological spaces is an equivalence
-- whose map and inverse map are both continuous.
#check Homeomorph

example (f : X ≃ₜ Y) : Continuous f := f.continuous_toFun
example (f : X ≃ₜ Y) : Continuous f.symm := f.continuous_invFun


example (f : X ≃ₜ Y) (x : X) : (𝓝 x).map f = 𝓝 (f x) := by
  exact Homeomorph.map_nhds_eq f x











































/- We can state that a topological space satisfies
separatedness axioms. -/

example : T0Space X ↔ Injective (𝓝 : X → Filter X) := by
  exact t0Space_iff_nhds_injective X

example : T1Space X ↔ ∀ x, IsClosed ({ x } : Set X) :=
  ⟨by exact fun a x ↦ isClosed_singleton, by exact fun a ↦ { t1 := a }⟩

example : T2Space X ↔
    ∀ x y : X, x ≠ y → Disjoint (𝓝 x) (𝓝 y) :=
  t2Space_iff_disjoint_nhds

example [T2Space X] {x y : X} (hxy : x ≠ y) :
    ∃ u v : Set X, u ∈ 𝓝 x ∧ v ∈ 𝓝 y ∧ (Disjoint u v) := by
  exact t2_separation_nhds hxy

example : RegularSpace X ↔ ∀ {s : Set X} {a},
    IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a) := by
  exact regularSpace_iff X










/- A set is compact if every open cover has a finite subcover. -/

example {K : Set X} : IsCompact K ↔ ∀ {ι : Type u}
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i := by
  exact isCompact_iff_finite_subcover

#check CompactSpace

/-
This can also be reformulated using filters.
* `NeBot F` iff `F ≠ ⊥` iff `∅ ∉ F`
* `ClusterPt x F` means that `F` has nontrivial intersection
  with `𝓝 x` (viewed as a generalized sets).
* `K` is compact iff every nontrivial filter that contains `K`
  has a cluster point in `K`.
-/

example (F : Filter X) : NeBot F ↔ F ≠ ⊥ := by
  exact neBot_iff

example {x : X} (F : Filter X) :
    ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) := by
  rfl

#check clusterPt_iff_not_disjoint
#check clusterPt_iff_forall_mem_closure

example {K : Set X} : IsCompact K ↔
    ∀ {F} [NeBot F], F ≤ 𝓟 K → ∃ x ∈ K, ClusterPt x F := by
  rfl

#check IsPreconnected
#check IsConnected
#check ConnectedSpace

end Topology














section Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/- A metric space is a type `X` equipped with a distance function
`dist : X → X → ℝ` with the following properties. -/

#check (dist : X → X → ℝ)
#check (dist_nonneg : ∀ {a b : X}, 0 ≤ dist a b)
#check (dist_eq_zero : ∀ {a b : X}, dist a b = 0 ↔ a = b)
#check (dist_comm : ∀ (a b : X), dist a b = dist b a)
#check (dist_triangle : ∀ (a b c : X), dist a c ≤ dist a b + dist b c)

/- In metric spaces, all topological notions are also
characterized by the distance function. -/

example (f : X → Y) (x₀ : X) : ContinuousAt f x₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ {x},
    dist x x₀ < δ → dist (f x) (f x₀) < ε :=
  Metric.continuousAt_iff

example (x : X) (ε : ℝ) :
    Metric.ball x ε = { y | dist y x < ε } := by
  rfl

example (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

#synth MetricSpace ℝ

-- Practice exercise: prove the sorry we had above.
example {x : X} : ⋂ i ∈ {s : Set X | IsOpen s ∧ x ∈ s }, i = {x} := by
  sorry
  done


end Metric



/-

Now you have time to do the teaching evaluations for this course.

Course ID: V3A6_F4A1-6
Password: qbfhzz9zv9kr
Link to the survey: https://www.umfragen.uni-bonn.de/lehre/Mathe/

Direct link to the survey (no manual entry necessary):
https://www.umfragen.uni-bonn.de/lehre/Mathe/?CourseID=V3A6_F4A1-6&Password=qbfhzz9zv9kr


If you have time after that, feel free to look at the exercise below or go home early.

-/


/- # Exercises

The goal of these exercise is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course Mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, sorry⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, sorry, sorry⟩

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by sorry

@[simp] lemma cl_int : U.cl.int = U := by sorry

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

/- We still have to prove that this gives a distributive lattice.
Note: these are hard; you might want to do the next exercises first. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  CompleteDistribLattice.ofMinimalAxioms
  { completeLattice with
    inf_sSup_le_iSup_inf := by sorry
    iInf_sup_le_sup_sInf := by sorry
    }


instance : HasCompl (RegularOpens X) := sorry


@[simp]
lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := by sorry


instance : CompleteBooleanAlgebra (RegularOpens X) :=
  { inferInstanceAs (CompleteDistribLattice (RegularOpens X)) with
    inf_compl_le_bot := by sorry
    top_le_sup_compl := by sorry
    le_sup_inf := by sorry
    sdiff_eq := by sorry
    himp_eq := by sorry }
