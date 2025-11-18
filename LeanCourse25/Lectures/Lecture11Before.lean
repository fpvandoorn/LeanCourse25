import Mathlib

open Function Set
noncomputable section

/- ## Last time

- define your own notation
- namespacing (and notation): `scoped` notation, `protected`, `section`s
- finiteness: `Finset`, `Fintype`, operations on finsets

* Over the next couple of classes we'll cover some topics in undergraduate mathematics, and see
  how this is done in Lean.
  - Group theory: group homomorphisms, subgroups, quotient groups, group actions,
    normal subgroups, index of a subgroup, some examples
  - Ring theory: ideals, units, polynomials
  - Linear algebra: linear maps, subspaces, endomorphisms, matrices, bases
  - Topology: Topological spaces, metric spaces, Hausdorff spaces, compact sets

-/


/- ## Today: group theory

Recall that we have additive and multiplicative classes, and the `@[to_additive] command
to translate between them. -/


/- # Monoids

The type of monoids structures on a type `M` with multiplicative notation is `Monoid M`.

The additive notation version is `AddMonoid`.
The commutative versions add the `Comm` prefix before `Monoid`. -/

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

/- Note in particular that `AddMonoid` exists, although it would be very confusing to use
additive notation in a non-commutative case on paper. -/





/- The type of morphisms between monoids `M` and `N`
is called `MonoidHom M N` and denoted by `M →* N`.
The additive version is called `AddMonoidHom` and denoted by `M →+ N`.

They both have a coercion to functions. -/

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) :
    f (x * y) = f x * f y := by
  sorry

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  sorry



/- Those morphisms are bundled maps,
i.e. they package together a map and some properties of this map.
Chapter 8 of Mathematics in Lean contain a lot more explanations about that
(https://leanprover-community.github.io/mathematics_in_lean/C08_Hierarchies.html).

Here we simply note the unfortunate consequence that we cannot use ordinary function composition.
We need to use `MonoidHom.comp` and `AddMonoidHom.comp`. -/

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f






/- # Groups and their morphisms -/

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := by sorry

/- Similar to the `ring` tactic that we saw earlier,
there is a `group` tactic that proves every identity
which follows from the group axioms
without using additional assumptions.
(hence one can see it as a tactic that
proves identities that hold in a free group). -/

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x*z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  sorry

/- And there is similar a tactic for identities
in commutative additive groups called `abel`. -/

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  sorry

/-
Groups morphisms are exactly monoid morphisms between groups
-/

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) :
    f (x * y) = f x * f y :=
  sorry

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) :
    f (x⁻¹) = (f x)⁻¹ :=
  sorry

/- Note that a map between group that preserves `*`
is automatically a group homomorphism. -/
example {G H : Type*} [Group G] [Group H] (f : G → H)
    (h : ∀ x y, f (x * y) = f x * f y) : G →* H :=
  sorry

/-
There is also a type `MulEquiv` of group (or monoid)
isomorphisms denoted by `≃*`
(and `AddEquiv` denoted by `≃+` in additive notation).
It works similar to `Equiv`.
The inverse of `f : G ≃* H` is `f.symm : H ≃* G`,
composition is `MulEquiv.trans` and
the identity isomorphism of `G` is `MulEquiv.refl G`.
This type is automatically coerced to morphisms and functions.
-/

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G := by exact?






/-
# Subgroups

In the same way group morphisms are bundled,
subgroups are also bundles made of a set in `G`
and some closure properties.
-/


example {G : Type*} [Group G] (H : Subgroup G) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H :=
  sorry

example {G : Type*} [Group G] (H : Subgroup G) : 1 ∈ H :=
  sorry

example {G : Type*} [Group G] (H : Subgroup G) {x : G}
    (hx : x ∈ H) : x⁻¹ ∈ H :=
  sorry

/-
In the above example, it is important to understand that
`Subgroup G` is the type of subgroups of `G`.
It is not a predicate on `Set G`.
It is endowed with a coercion to `Set G`
and a membership predicate on `G`.
See Chapter 8 of Mathematics in Lean for explanations
about why and how things are set up like this.

Of course the type class instance system knows
that a subgroup of a group inherits a group structure.
-/

example {G : Type*} [Group G] (H : Subgroup G) : Group H := by sorry

/-
Here `H` is coerced to the subtype `{x : G // x ∈ H}`,
just like a set.
-/

example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := by sorry

/-
An important benefit of having a type `Subgroup G`
instead of a predicate `IsSubgroup : Set G → Prop`
is that one can easily endow it with additional structure.
Crucially this includes a complete lattice structure
with respect to inclusion (denoted `≤` in Lean).
For instance, instead of having a lemma stating that an intersection
of two subgroups of `G`, we have the lattice operation `⊓`
and all lemmas about lattices are readily available.
-/

example {G : Type*} [Group G] : CompleteLattice (Subgroup G) := by sorry

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := by rfl

example {G : Type*} [Group G] (H H' : Subgroup G) : H ⊓ H' ≤ H := by sorry

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  sorry


















  --simp [Subgroup.closure_union]

/-
Another subtlety is `G` itself does not have type `Subgroup G`,
so we need a way to talk about `G` seen as a subgroup of `G`.
This is also provided by the lattice structure.
We are talking about the top element of this lattice.
-/

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) :=
  trivial

/-
Similarly the bottom element of this lattice is the subgroup
whose only element is `1`.
-/

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 :=
  Subgroup.mem_bot



/- One can pushforward (image) and pullback (preimage)
of subgroups with respect to a morphism. -/

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  sorry

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  sorry



/- Two important subgroups are the kernel and the range of a homomorphism. -/

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  sorry

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  sorry


/- Normal subgroups are stated using an `IsNormal` class. -/

variable {G : Type*} [Group G] (H : Subgroup G)
#check H.Normal

-- The kernel of a group homomorphism is always a normal subgroup.
-- Exercise: try to state this yourself, and prove it.


-- Any subgroup of an abelian group is a normal subgroup.
-- Exercise: state and prove this yourself.
example {G : Type*} [CommGroup G] (H : Subgroup G) : H.Normal := by
  exact Subgroup.normal_of_comm H




/- # Quotient groups -/

/-
The quotient of a group `G` by a normal subgroup `H` is denoted `G ⧸ H`.
If `H` is not normal, this stands for the left cosets of `H`.

-/

section QuotientGroup

/- If `H` is an arbitrary subgroup, `G ⧸ H` is the type of left cosets
of `H`. -/
example {G : Type*} [Group G] (H : Subgroup G) : Type _ := G ⧸ H

/- If `H` is normal, this type can be equipped with a group structure. -/
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := by sorry

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H

/- The universal property of quotient groups -/
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  sorry

/- The first isomorphism theorem -/
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ ≃* MonoidHom.range φ :=
  sorry

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G'⧸ N':=
  sorry

end QuotientGroup


/- # Index of a subgroup

The index of a subgroup `H` of a group `G` is the cardinality of the space `G / H` of left cosets.
If this space is infinite, the index is `0`.
If `H` is a normal subgroup of finite index, this index is the cardinality of the quotient group.

-/
section Index

variable {G : Type*} [Group G] (H : Subgroup G)

#check H.index

-- The trivial subgroup in the integers has index 0, as ℤ is infinite.
#check (⊥ : AddSubgroup ℤ).index

-- If a subgroup has index two, it is normal.
example (hH : H.index = 2) : H.Normal := sorry

-- Given a type `α`, a *permutation* of `α` is a bijective map `α → α`.
-- The collection of all permutations of `α` forms a group, the **permutation group** on `α`.
#check Equiv.Perm ℤ

#check Equiv.Perm (Fin 5)

open scoped Nat -- activate factorial notation

-- The permutation group on `n` symbols has `n!` elements.
example {n : ℕ} : Nat.card (Equiv.Perm (Fin n)) = (n)! := by
  sorry
  -- let's use rw?? to find a proof

-- Each permutation has a sign: the **alternating group** is the subgroup of all *even*
-- permutations, i.e. those with positive sign.
#check Equiv.Perm.sign

#check alternatingGroup

variable {α : Type*} [Fintype α] [DecidableEq α]

example (σ : Equiv.Perm α) : σ ∈ alternatingGroup α ↔ Equiv.Perm.sign σ = 1 := by
  rfl

-- The alternating group is a normal subgroup and has index two.
example : (alternatingGroup α).index = 2 := by sorry

example : (alternatingGroup α).Normal := sorry
#check alternatingGroup.isSimpleGroup_five

-- For n ≥ 5, the alternating group in n letters is simple: it has no non-trivial subgroups.
#check IsSimpleGroup
#check Subgroup.isSimpleGroup_iff

example : IsSimpleGroup (alternatingGroup (Fin 5)) := sorry

end Index
