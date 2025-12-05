import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.MetricSpace.Contracting

open BigOperators Function Set Real Topology Filter
open Interval ENNReal
noncomputable section

/- # Last time

Last time we discussed topology:
* `TopologicalSpace X` states that `X` is a topological space.
* continuity via `Filter.Tendsto` and via open sets
* homeomorphisms; compactness; connectedness
* various separation axioms
* the `fun_prop` tactics for proving goals of the form
  "the composition of continuous functions is continuous"
* `MetricSpace X` states that `X` is a metric space.


Today: differential calculus and differentiation
-/




/- # Differential Calculus -/

/- We write `deriv` to compute the derivative of a function.
`simp` can compute the derivatives of standard functions. -/

example (x : ℝ) : deriv Real.sin x = Real.cos x := by simp

example (x : ℂ) :
    deriv (fun y ↦ Complex.sin (y + 3)) x = Complex.cos (x + 3) := by simp

/- Not every function has a derivative.
As usual, in Mathlib we just define the derivative
of a non-differentiable function to be `0`. -/

variable (f : ℝ → ℝ) (x : ℝ) in
#check (deriv_zero_of_not_differentiableAt :
  ¬ DifferentiableAt ℝ f x → deriv f x = 0)

/- So proving that `deriv f x = y` doesn't
necessarily mean that `f` is differentiable.
Often it is nicer to use the predicate `HasDerivAt f y x`,
which states that `f` is differentiable and `f'(x) = y`. -/

example (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x :=
  hasDerivAt_sin x


/- We can also specify that a function has a derivative
without specifying its derivative. -/

example (x : ℝ) : DifferentiableAt ℝ sin x :=
  differentiableAt_sin

-- Note: the argument `ℝ` is the field over which we are working,
-- not the domain of the sin function.
-- For instance, this is how to say "the Complex sin function is real differentiable".
example (z : ℂ) : DifferentiableAt ℝ Complex.sin z := sorry


#check HasDerivAt.differentiableAt

/- Mathlib contains lemmas stating that common operations satisfy
`HasDerivAt` and `DifferentiableAt` and to compute `deriv`. -/

#check HasDerivAt.add
#check deriv_add
#check DifferentiableAt.add


example (x : ℝ) :
    HasDerivAt (fun x ↦ Real.cos x + Real.sin x)
    (Real.cos x - Real.sin x) x := by
  rw [sub_eq_neg_add]
  apply HasDerivAt.add
  · exact hasDerivAt_cos x
  · exact hasDerivAt_sin x
  done


/- There are various variations of derivatives/being differentiable -/

/- A function is differentiable everywhere. -/
#check Differentiable

/- A function is differentiable on a subset. -/
#check DifferentiableOn

/- A function is differentiable at a point, considered only within the subset -/
#check DifferentiableWithinAt

/- We can also consider the derivative only within a subset. -/
#check HasDerivWithinAt
#check derivWithin




/-
Recall Lean's notation for intervals: `Icc a b = [a, b]` is a closed interval

The **intermediate value theorem** states that if `f` is continuous and
`f a ≤ y ≤ f b`, then there is an `x ∈ [a, b]` with `f(x) = y`.
-/

example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  intermediate_value_Icc hab hf

-- There is also a version for `f a ≥ y ≥ f b`, and one for unordered intervals.
-- `Set.uIcc a b` denotes the *unordered* closed interval `[[a, b]]`:
-- depending on whether `a ≤ b` or `b ≤ a`,
-- it is either `Icc a b` or `Icc b a`.
#check Set.uIcc


/- The deeper mathematical reason is that intervals are connected (and vice versa).
Continuous functions preserve connectedness.
-/
#check isConnected_Icc
#check IsPreconnected.mem_intervals

#check IsConnected.image

#check IsConnected.Icc_subset

-- Let's put this together ourselves.
example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b := by
  have : IsConnected (Icc a b) := isConnected_Icc hab
  have : IsConnected (f '' Icc a b) := this.image f hf
  apply this.Icc_subset
  · refine mem_image_of_mem f ?_
    exact left_mem_Icc.mpr hab
  · apply mem_image_of_mem
    exact right_mem_Icc.mpr hab









/-
The mean value theorem states that if `f` is continous on `[a, b]`
and differentiable on `(a, b)` then there is a `c ∈ (a, b)` where `f'(c)` is the
average slope of `f` on `[a, b]`
-/
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'


/- Rolle's theorem is the special case where `f a = f b`.
Why is there no differentiability requirement on `f` here? -/
example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI



/- We can more generally talk about the derivative of functions between normed spaces.

A *normed group* is an abelian group with a norm satisfying the following rules.
-/

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

#check (fun x ↦ ‖x‖ : E → ℝ)

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

/- This turns `E` into a metric space. -/
example : MetricSpace E := by infer_instance
/- The metric is induced by the norm. -/
example (x y : E) : dist x y = ‖x - y‖ := by
  exact NormedAddGroup.dist_eq x y



/- A *normed space* is a normed group that is a vector space
satisfying the following condition. -/

variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ := by
  rw [norm_smul a x]
  rw [norm_eq_abs]


/- A complete normed space is known as a *Banach space*.
Every finite-dimensional vector space is complete. -/

example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance

-- Products of Banach spaces are also Banach.
example [CompleteSpace E] : CompleteSpace (E × E) := by infer_instance

-- A quotient of a Banach space is also Banach.
example [CompleteSpace E] (s : Submodule ℝ E) : CompleteSpace (E ⧸ s) := by infer_instance

-- The Banach fixed point theorem
#check ContractingWith.exists_fixedPoint

/- In the above examples, we could also replace `ℝ` by `ℂ`
or another *normed field*. -/
#check NormedField


#check TopologicalSpace.SeparableSpace

-- The continuous dual space: all continuous linear maps `E →L[R] R`
#check StrongDual

#check Module.IsReflexive

-- Hahn-Banach theorem
#check exists_extension_norm_eq

-- Banach-Alaoglu theorem
#check WeakDual.isCompact_polar

-- Mathlib also has the closed graph theorem.

end NormedGroup



/- We can also take the derivative of functions that take values in a
normed vector space. -/

/- This is why we need to specify the base field in `DifferentiableAt`:
for instance, a complex normed space is also a real normed space,
and being complex differentiable is stronger than being real differentiable. -/


-- Proving differentiability is easy using `fun_prop`.
example {x : ℝ} : DifferentiableAt ℝ (fun x ↦ ((Real.cos x) ^ 2, (Real.sin x) ^ 2)) x := by
  fun_prop

-- Currently, derivatives still have to be computed by hand.
example (x : ℝ) : deriv (fun x ↦ ((Real.cos x) ^ 2, (Real.sin x) ^ 2)) x =
    (- 2 * Real.cos x * Real.sin x, 2 * Real.sin x * Real.cos x) := by
  apply HasDerivAt.deriv
  refine HasDerivAt.prodMk ?_ ?_ -- apply?
  · -- Careful: the `suffices` tactic has syntax involving `by`, but **not** `:= by`!
    suffices HasDerivAt (fun x ↦ cos x ^ 2) (2 * (cos x) ^ 1 * (- sin x)) x by
      -- Other proofs would be `simp_all` or `simpa`.
      -- `simp_all` simplifies both the goal and all local hypotheses, using all local hypotheses.
      -- `simpa` is shorthand for `simp; assumption`. You can also provide an explicit
      -- term to prove the goal: writing `simpa using h` runs `simp` on the goal and on `h`.
      -- If the simplified `h` does not prove the goal, it fails.
      field_simp at this ⊢
      exact this
    apply HasDerivAt.pow
    exact hasDerivAt_cos x
  · -- The `convert` tactic is similar to `refine`: it tries to match the term
    -- provided to it with the goal and creates a new goal for each goal
    -- that you need to prove, and each part of the term that does not match exactly.
    -- In this case, there are two goals, one about unifying `sin x ^ {2 - 1}` and `sin`,
    -- and another about `HasDerivAt` and `sin`.
    convert HasDerivAt.pow ?_ 2
    · simp
    · exact hasDerivAt_sin x
  done



/- If the domain is a normed space we can define the
total derivative, which will be a continuous linear map. -/

/- Morphisms between normed spaces are continuous linear maps `E →L[𝕜] F`. -/
section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]


example : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F := f

example (f : E →L[𝕜] F) : Continuous f := f.cont

example (f : E →L[𝕜] F) : E →ₗ[𝕜] F := f

example (f : E →L[𝕜] F) (g : F →L[𝕜] G) : E →L[𝕜] G := g.comp f

/- Isomorphisms between normed spaces are continuous linear equivalences `E ≃L[𝕜] F` -/
example : E ≃L[𝕜] E := ContinuousLinearEquiv.refl 𝕜 E

-- We can invert and compose continuous linear equivalences: these operations are called
-- `symm` and `trans`, like for linear equivalences.
example (f : E ≃L[𝕜] F) : F ≃L[𝕜] E := f.symm

example (f : E ≃L[𝕜] F) (g : F ≃L[𝕜] G) : E ≃L[𝕜] G := f.trans g



/- Continuous linear maps have an operator norm. -/

example (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  ContinuousLinearMap.le_opNorm f x

example (f : E →L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  (ContinuousLinearMap.opNorm_le_iff hMp).mpr hM


/- We define the *Fréchet derivative* of any function between normed spaces. -/

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔
    Tendsto (fun x ↦ ‖f x - f x₀ - f' (x - x₀)‖ / ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
  rw [hasFDerivAt_iff_tendsto]
  field_simp
  -- or: simp_rw [div_eq_inv_mul, hasFDerivAt_iff_tendsto]

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) :
    fderiv 𝕜 f x₀ = f' :=
  HasFDerivAt.fderiv hff'

-- Like for the derivative, we also have a Fréchet derivative within a set.
variable (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x₀ : E) in
#check fderivWithin 𝕜 f s x₀

#check HasFDerivWithinAt.fderivWithin


-- Careful: in higher dimensions, a function can have several derivatives within a set,
-- if that set is sufficiently "bad".
-- However, on "nice" sets, it is: this includes open sets and convex sets with non-empty interior.
#check UniqueDiffOn

example {s : Set E} (hs : IsOpen s) : UniqueDiffOn 𝕜 s := hs.uniqueDiffOn

#check Convex
#check uniqueDiffOn_convex





/- We can take the directional derivative or partial derivative
by applying the Fréchet derivative to an argument -/
example (x y : ℝ) :
    let f := fun ((x,y) : ℝ × ℝ) ↦ x^2 + x * y
    fderiv ℝ f (x, y) (1, 0) = 2 * x + y := by
  sorry -- exercise


/- We write `ContDiff 𝕜 n f` to say that `f` is `C^n`,
i.e. it is `n`-times continuously differentiable.
Here `n` lives in `WithTop ℕ∞`:
`ℕ∞` is `ℕ` with an extra top element `∞` added ("∞"),
and `WithTop ℕ∞` adds another element `⊤` ("ω").
-/
variable {f g : E → F} {m : ℕ∞} {r : 𝕜}

open scoped ContDiff -- for the notation "∞"

#check ContDiff 𝕜 37 f
#check ContDiff 𝕜 ∞ f -- f is smooth



example : ContDiff 𝕜 0 f ↔ Continuous f := contDiff_zero

example {n : ℕ} : ContDiff 𝕜 (n+1) f ↔
    Differentiable 𝕜 f ∧ ContDiff 𝕜 n (fderiv 𝕜 f) := by
  simp [contDiff_succ_iff_fderiv]


example : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f :=
  contDiff_infty



/- The element ω denotes analytic functions: those which have a Taylor series which converges
to the function -/
#check ContDiff 𝕜 ω f -- f is analytic

#check AnalyticAt

example [CompleteSpace F] : ContDiff 𝕜 ω f ↔ ∀ x, AnalyticAt 𝕜 f x := sorry

/- `fun_prop` can also prove that simple functions are `C^n`,
and knows about the relation between differentiability and `C^n` functions -/
variable {f g : E → F} {n : ℕ∞} {r : 𝕜}
example (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x ↦ (f x, r • f x + g x)) := by
  fun_prop

/- To summarise:
To prove differentiability goals, you can use
- (sometimes) use `simp` for goals `(f)deriv f x = y`
- use simp or argue by hand for goals `Has(F)DerivAt f f' x`
- use `fun_prop` for function properties like `DifferentiableAt` or `ContDiff`
-/

-- The implicit function theorem
#check ImplicitFunctionData.implicitFunction

-- The inverse function theorem
#check HasStrictFDerivAt.to_localInverse

/- If `f` is C¹, its `fderiv` is continuous -/
#check ContDiff.continuous_fderiv

-- There is also a converse: if `f` is differentiable and has continuous fderiv, it is C¹.
#check contDiff_one_iff_fderiv

-- This also holds for higher smoothness.
#check contDiff_succ_iff_fderiv


-- We can also take higher derivatives: these are denoted `iteratedFDeriv`
#check iteratedFDeriv

-- If `f : E → F`, then `fderiv 𝕜 f x : E →L[𝕜] F` is a continuous linear map.
#check fderiv 𝕜 f

-- The `fderiv` of that is a continuous bilinear map, and so on:
variable {x₀ : E}
#check iteratedFDeriv 𝕜 2 f x₀

#check ContinuousMultilinearMap

-- The 0-th iterated fderiv is the function itself.
#check iteratedFDeriv_zero_apply

-- The first iterated fderiv is the fderiv.
-- Strictly speaking, their types are slightly different.
example (m : Fin 1 → E) : iteratedFDeriv 𝕜 1 f x₀ m = (fderiv 𝕜 f x₀) (m 0) := by
  exact iteratedFDeriv_one_apply m

-- The k+1-th iterated fderiv is the fderiv of the k-th one.
#check iteratedFDeriv_succ_apply_left

end NormedSpace
