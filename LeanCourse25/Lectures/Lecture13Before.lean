import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.ComputeDegree

import Mathlib.Algebra.Group.Action.Prod
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace

open Function Set Polynomial
noncomputable section

/- ## Last time

- it may be best to avoid a bare `import Mathlib` at the top of your file
- start thinking about project 2: your own formalisation project
   - see `Project 2.md` in the `Project` folder
   - if you use AI, please mention this explicitly in the final report
   - please check with Floris van Doorn and me if your project topic is suitable
     (e.g., feasible, suitable scope, not done before)
- short group theory addendum
- ring theorem: rings, subrings, ideals; ring homomorphisms, Chinese remainder theorem
- algebras, polynomials and tactics for them

-/

/- ## Today: linear algebra -/

/- ### Group actions-/

section GroupAction

/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

/-
The dot • (typed as `\smul` in VS Code) denotes scalar multiplication: a multiplicative action
assumes you have a "scalar multiplication" instance on your type.
(We will encounter this later today when talking about vector spaces and modules.)
-/

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact? -- sorry
example (x : X) : (1 : G) • x = x := by exact? -- sorry

-- In your algebra course, you might have seen a different definition, of a group action as a
-- group homomorphism `G → S_X` to the permutation group on `X`: Lean knows this also.
#check MulAction.toPermHom

-- If you want to just want to know the permutation induced by one particular element, use `toPerm`.
#check MulAction.toPerm

-- There is also a typeclass for additive actions
#check AddAction


/- Let's give an example: there are at least three actions of any group on itself
(1) doing nothing: `g • x = x` for all g and x
(2) acting by multiplication: `g • x = g * x`
(3) acting by conjugation: `g • x = g * x * g⁻¹`

Mathlib has such an instance already: which one does it use?
The #synth command asks Lean "find this instance using typeclass synthesis, and tell me how it is
called".
-/
#synth MulAction G G

-- Let's look at the definition of the action to see which one it is.
-- #check Monoid.toMulAction G

-- We can even verify this ourselves.
example {g g' : G} : g • g' = g * g' := by sorry -- simp?



-- Let's add another definition, of the trivial action of G on itself.
instance trivialAction : MulAction G G where
  smul g x := x
  one_smul x := by sorry
  mul_smul := by sorry

example {g x : G} : g • x = x := by rfl

-- Note that Lean finds a different action now.
#synth MulAction G G


-- This is how to define the action of `G` on itself by conjugation.
instance conjugationAction : MulAction G G where
  smul g x := sorry -- g * x * g⁻¹
  one_smul x := by sorry
  mul_smul g h x := by
    sorry

#synth MulAction G G

-- Note: `MulAction` is a class, and we just defined three different instances of it.
-- Typeclass search will find these instances, but you shouldn't always expect it to find
-- the same one: if you want to consider e.g. "G with this particular action", this is not very
-- robust yet. (One more robust way is a type synonym, which we may mention towards the end of
-- the course.)



-- A group acts on its subgroups by conjugation: this is what the current assignment is about.


-- Lean knows about the diagonal action of a group on itself.
instance : MulAction G (X × X) := by infer_instance
example {g h k : G} : g • (h, k) = (g • h, g • k) := rfl

-- Let's tell it about the product action: if G acts on X, then G × G acts on X × X.
example : MulAction (G × G) (X × X) where
  smul := sorry -- fun ⟨g, h⟩ ⟨x, y⟩ ↦ ⟨g • x, h • y⟩
  one_smul x := by
    sorry
  mul_smul g h x := by
    sorry


end GroupAction



section LinearAlgebra

/- # Modules and vector spaces

Most results in linear algebra are not formulated in terms of vector spaces,
but instead they are generalized to modules over a (semi)ring.
To state that `V` is a vector space over `K`, we actually use the word `Module`.
Note that we have to separately state that `(V, +)` is a group.
Scalar multiplication is written with `•` (\smul). -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

example (k : K) (v : V) : -k • v = k • -v := by
  sorry -- use rw??

/- Beware: every group also has a scalar multiplication w.r.t.
`ℕ` and `ℤ`, and the following lemmas relate this to the
scalar multiplication of `K`. -/

example (v : V) : (2 : K) • v = (2 : ℕ) • v :=
  sorry
  -- Nat.cast_smul_eq_nsmul K 2 v
example (v : V) : (2 : ℤ) • v = (2 : K) • v := by
  sorry
  -- simp [← Int.cast_smul_eq_zsmul K 2 v]


/- A module `M` over a ring `R` is an abelian group `(M, +)`
together with a scalar multiplication `R → M → M`
with appropriate associativity and distributivity laws. -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (r : R) (x y : M) : r • (x + y) = r • x + r • y := by exact? -- sorry
example (r s : R) (x : M) : (r + s) • x = r • x + s • x := by exact? -- sorry
example (r s : R) (x : M) : (r * s) • x = r • s • x := by exact? -- sorry
example (x : M) : (0 : R) • x = 0 := by exact? -- sorry
example (x : M) : (1 : R) • x = x := by exact? -- sorry
example (r : R) : r • (0 : M) = 0 := by exact? -- sorry

/- As usual, we have submodules and quotients
Note that the quotient symbol is *not* the usual forward slash! -/
example (S : Submodule R M) : Module R (M ⧸ S) := by infer_instance


/- We have linear maps `M →ₗ[R] N` between modules.
We have to write `R` explicitly in this notation.

For example, in complex analysis there is an important difference
between `ℝ`-linear maps and `ℂ`-linear maps -/
variable {N N' : Type*}
  [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

/- `N × N'` is a biproduct: it is both the
product and coproduct of the modules `N` and `N'`. -/
example (f : M →ₗ[R] N) (g : M →ₗ[R] N') :
  M →ₗ[R] N × N' where
    toFun := fun m ↦ (f m, g m)
    map_add' := by sorry
    map_smul' := by sorry

example : M →ₗ[R] M × N := LinearMap.inl R M N
example : N →ₗ[R] M × N := LinearMap.inr R M N
example : M × N →ₗ[R] M := LinearMap.fst R M N
example : M × N →ₗ[R] N := LinearMap.snd R M N


-- The kernel of a linear map is a submodule, as is its range.
variable (f : M →ₗ[R] N)
#check LinearMap.ker f
#check LinearMap.range f

/-
A linear maps is injective if and only if its kernel is trivial.
Note again the notation `⊥` for the zero submodule:
as you may have guessed, the full submodule is denoted `⊤`,
and the submodules of a given module form a complete lattice.
-/

#check (⊥ : Submodule R M)
example {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 := by sorry

#check (⊤ : Submodule R M)
#check Submodule.mem_top

example (f : M →ₗ[R] N) : LinearMap.ker f = ⊥ ↔ Injective f := by sorry

example : CompleteLattice (Submodule R M) := by infer_instance


/- Linear maps themselves form a module over `R`
(requires that `R` is a commutative ring) -/
example : Module R (M →ₗ[R] N) := by infer_instance

/- If you want to use an operation that is linear in multiple arguments,
you can write it as a bundled morphism into the type of bundled morphisms. -/
#check LinearMap.lsmul R M
example (r : R) (m : M) : LinearMap.lsmul R M r m = r • m := by rfl
example (f : M →ₗ[R] N →ₗ[R] N') : N →ₗ[R] M →ₗ[R] N' := f.flip



/- We also have linear equivalences between modules: we write these as `M≃ₗ[R] N` -/
#check M ≃ₗ[R] N

/- A linear equivalence sometimes must be converted explicitly to a linear map,
but in many cases a coercion to linear maps applies directly. -/
example (f : M ≃ₗ[R] N) : Submodule R M := LinearMap.ker f
example (f : M ≃ₗ[R] N) : Submodule R N := LinearMap.range f
example (f : M ≃ₗ[R] N) : M →ₗ[R] N := f.toLinearMap

-- A linear equivalence is a linear map which is surjective and injective.
example (f : M →ₗ[R] N) (hf : Bijective f) : M ≃ₗ[R] N := sorry

-- An injective linear map induces a linear equivalence to its range.
example (f : M →ₗ[R] N) (hf : Injective f) : M ≃ₗ[R] LinearMap.range f :=
  sorry

-- Trick question: what happens if we just write "range f"?
-- example (f : M →ₗ[R] N) (hf : Injective f) : M ≃ₗ[R] range f :=
--  LinearEquiv.ofInjective f hf

-- The **first isomorphism theorem** for modules: the quotient of M by ker f is equivalent
-- to the range of f.
example (f : M →ₗ[R] N) : (M ⧸ (LinearMap.ker f)) ≃ₗ[R] LinearMap.range f :=
  sorry

-- In particular, for a surjective linear map, the quotient of M by ker f is equivalent to N.
example {f : M →ₗ[R] N} (hf : Surjective f) : (M ⧸ (LinearMap.ker f)) ≃ₗ[R] N :=
  sorry


/- ## Linear algebra: endomorphisms, trace and determinant, and matrices -/


/- Matrices are defined in Mathlib, but generally we prefer to work
abstractly with vector spaces (or modules) without choosing a basis.
Things are often easier when stated using linear maps than with matrices. -/
#check Matrix

open scoped Matrix
example {m n : Type*} (M : Matrix m n M) : Mᵀᵀ = M := rfl

-- For example, we can define the determinant and trace for an linear endomorphism,
-- not just for a matrix.
section

variable {m : Type*} (A : Matrix m m M) [DecidableEq m] [Fintype m] [CommRing M]

#check A.det

#check A.trace

variable {V : Type*} [AddCommGroup V] [Module R V] {f : V →ₗ[R] V}

#check f.det
#check f.trace R V

end

/- We use `ι → ℝ` to denote `ℝ^n` if `ι` has `n` elements.
However, it is nicer to work over an abstract (finite-dimensional)
vector space. -/
example {ι : Type*} (v : ι → ℝ) : v + v = 2 • v := by rw [two_smul]
example {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (v : V) : v + v = 2 • v := by rw [two_smul]

/- `Module.finrank` gives the dimension of a vector space. -/
#check Module.finrank R M

/- `Module.Basis ι R M` is a structure of a basis of a vector space.
It is given by an equivalence of `M` with `ι →₀ R`, which is the
(infinitary) coproduct of copies of `R`, vectors indexed by `ι`,
where only finitely many entries are nonzero. -/
example {ι : Type*} (b : Module.Basis ι R M) : M ≃ₗ[R] ι →₀ R := b.repr

open Module

example {ι : Type*} (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  sorry

/- As said above, you should avoid working with matrices when you can use linear maps instead.
If you must absolutely convert to matrices, mathlib also ha this: given a choice of basis,
you can convert a linear map to its induced matrix. This only works in finite dimensions and
requires a technical condition (decidable equality) on the indexing type. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (f : V →ₗ[K] V) : Matrix ι ι K := sorry -- LinearMap.toMatrix b b f

example  {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (f : V →ₗ[K] V) : f.det = (f.toMatrix b b).det :=
  sorry -- (LinearMap.det_toMatrix b f).symm

/- ### Eigenvectors, eigenvalues etc. -/

variable {f : V →ₗ[K] V} {v : V} {a : K}
-- Is `v` an eigenvector for the value `a` of an endomorphism `f`?
#check End.HasEigenvector f a v
-- Is `a` an eigenvalue of an endomorphism `f`?
#check End.HasEigenvalue f a

-- If `v` is an eigenvector for `a`, then `a` is an eigenvalue.
example (hv : End.HasEigenvector f a v) : End.HasEigenvalue f a :=
  sorry

-- The characteristic polynomial of a linear map (assuming `V` is finite-dimensional).
variable [FiniteDimensional K V] in
#check f.charpoly

-- The characteristic polynomial is monic, has degree n (where n is the dimension of V),
-- and its constant coefficient is (up to sign) the determinant,
-- i.e. the product of its eigenvalues.
#check LinearMap.charpoly_monic
#check LinearMap.charpoly_natDegree
#check LinearMap.det_eq_sign_charpoly_coeff
-- The first coefficient after the leading one is the opposite of the trace.
-- Polynomial.nextCoeff is the second-highest coefficient (or zero).
#check Matrix.trace_eq_neg_charpoly_nextCoeff
#check Polynomial.nextCoeff


-- The Cayley-Hamilton: evaluation the characteristic polynomial of f at f yields zero.
#check LinearMap.aeval_self_charpoly


section product

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/- We can also take a (infinitary) product of modules.
This is given by the `Π`-type or dependent function type in Lean.
-/
example : Module R (Π i, M i) := by infer_instance

example (f : Π i, M i) (i : ι) : M i := f i

open Classical in
example (f : Π i, M i) (i₀ : ι) (x : M i₀) :
  Π i, M i := fun j : ι ↦ Function.update f i₀ x j

example (r : R) (f : Π i, M i) (i : ι) :
  (r • f) i = r • f i := by sorry

open Classical in
example (r : R) (f : Π i, M i) (i₀ : ι) (x : M i₀) :
    r • Function.update f i₀ x = Function.update (r • f) i₀ (r • x) := by
  sorry
  done

end product

end LinearAlgebra
