## Project 2: your own formalisation project

## Personal Info

Please fill out the following. Fill in the project topic once you have decided.
```
First & last name:
Project topic:
Partner (optional):
```

## Your own project

During the second half of the course you will work on a project in any area of mathematics of your choice. You can put your project files in this folder.

Since a project likely consists of more than 1 file, it will be useful to publish this as a repository on GitHub.

You can work on your project in groups of two (and we recommend doing so).
`Git.md` has a section `Working with a partner` about handling this in git.

## Formalization Topics

You can choose a topic in any area of mathematics.
Please enter your project topic in [this table](https://uni-bonn.sciebo.de/s/tBzqggEFajsgwC6), and ask Floris van Doorn or Michael Rothgang to approve your project topic.


A good topic should be
* not yet in mathlib (although it's also fine to give a different proof of something already in mathlib);
* not too hard (don't overestimate how much you can do in your project);
* not require too many prerequisites that are not yet part of mathlib.

On the mathlib website there are some useful pages:
* [topics in mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [undergraduate topics in mathlib](https://leanprover-community.github.io/undergrad.html)
* [the full contents of mathlib](https://leanprover-community.github.io/mathlib4_docs/) (use the search in the top right)


Some suggested topics:

* In **analysis**: the Fourier transform and convolution have been defined in mathlib. Show that the Fourier transform of a convolution is the product of Fourier transforms.

* In **calculus**: prove the gradient theorem for Euclidean space, also know as the fundamental theorem of calculus for line integrals. As stretch goals use it to prove the equivalence of two definitions of a conservative vector field and provide an example of a non-conservative vector field.

* In **real analysis**:
  - show that the Weierstrass function is continuous but nowhere differentiable.
  `tendstoUniformly_tsum` and `TendstoUniformly.continuous` will be useful to show the continuity.
  - show that nowhere differentiable functions are dense in the space of continuous functions
  - prove **Tikhonov’s theorem:** let K be a nonempty compact set in a normed space. Then any continuous function K → K has a fixed point

* In **complex analysis**
  - Prove that the Laurent series for a complex function converges on an annulus.

* In **combinatorics**: prove **Schur’s theorem:** for any coloring of the natural numbers in finitely many colors, there exists a monochromatic triple x, y, z such that x + y = z.

* In **commutative algebra**: Prove the [Krull–Akizuki theorem](https://en.wikipedia.org/wiki/Krull%E2%80%93Akizuki_theorem)

* In **Computability**
  * Show that the problem “is x = 1 in a given semigroup defined by generators and relations?” is undecidable.
  * **Computational complexity:** this area is in an early stage in Mathlib. Currently, only the class **P** is defined. You could define **NP** and provide an example of an NP-hard problem (even a trivial one — or try the Cook–Levin theorem).

* In **differential geometry**
  - define differential 1-forms and exact 1-forms (closed 1-forms are harder to define).
    Show that on a simply connected domain, every 1-form is exact. (Mathlib is still missing a general definition of n-forms, but that is too hard for a project)
  - Prove that a diffeomorphism between connected manifolds is either orientation-preserving or orientation-reversing (copy-paste the definition of orientable manifold from Mathlib PR [#16239](https://github.com/leanprover-community/mathlib4/pull/16239/files) and assume your manifolds have no boundary).
  - prove (parts of the) classification of connected 1-manifolds. (We can provide a good reference to start.)
  - define quotients of manifolds: if G is a discrete group acting properly on a manifold M, prove that the quotient M/G is a smooth manifold. Option/stretch goal: construct the real projective space from the sphere.

* In **hyperbolic geometry** define the Poincaré model of hyperbolic geometry - either the disc model or the half-plane model (or another model altogether), and show that is satisfies most of Euclid's axioms for geometry, but that the parallel postulate fails.

* In **planar geometry** many results are missing. Choose one: Desargues's theorem, Feuerbach's theorem, Menelaus's theorem, Morley's trisecor theorem.

* In **group theory**, study concrete group presentations. Mathlib has a `PresentedGroup` structure, but no concrete examples yet. For example, you could formalize the presentation of the permutation group (or others from [here](https://en.wikipedia.org/wiki/Presentation_of_a_group#Examples).

* In **linear algebra**/**geometry**: prove the **Cartan–Dieudonné theorem:** every isometry of ℝⁿ can be represented as a composition of at most n reflections.

* In **linear algebra**, prove Sylvester’s criterion for the positive definiteness of Hermitian matrices

* In **measure theory**, prove **Luzin’s theorem:** a function f is measurable on [0, 1] if and only if for every ε > 0, there exists a compact set of measure greater than 1 − ε on which f is continuous.

* In **model theory**: complete types of a language are defined in mathlib. Prove for a countable theory that if there are uncountably many types with `n` free variables, then there are continuum many. Or harder: show that in this case that the theory has continuum many non-isomorphic models.

* In **number theory**:
  - Prove the Hasse-Minkowski theorem for quadratic forms of the form `a_1*X_1^2 + a_2 * X_2^2`. If you have time, prove the `n = 3` case `(a_1*X_1^2 + a_2 * X_2^2 + a_3 * X_3^2)`.
  - Solve some diophantine equations. For example: show that there are no nonzero integer solutions to `x^4-y^4=z^2`. Find all solutions to `x^2+y^2=z^3` and to `|2^k-3^l|=1`.
  - **Hurwitz’s theorem** ([ProofWiki link](https://proofwiki.org/wiki/Hurwitz%27s_Theorem_(Number_Theory))) on approximating irrational numbers by rationals.

* In **order theory**: Define the [Boolean completion](https://en.wikipedia.org/wiki/Complete_Boolean_algebra#The_completion_of_a_Boolean_algebra) of a Boolean algebra

* In **set theory**:
  - Define weakly compact cardinals, and prove that some other (combinatorial) properties are equivalent to this definition, e.g. properties 1-4 from [Wikipedia](https://en.wikipedia.org/wiki/Weakly_compact_cardinal).
  - Define generalized stationarity and prove Fodor's lemma for this: https://en.wikipedia.org/wiki/Stationary_set#Generalized_notion

* In **topology**:
  - [general topology] Define the Möbius strip and/or the Klein bottle and prove basic properties (e.g.: different constructions are equivalent; boundary of Möbius strip is connected and homotopy equivalent to `S¹`)
  Optional: prove they are smooth manifolds (with boundary).
  - [general topology] Define the [long line](https://en.wikipedia.org/wiki/Long_line_(topology)) and show that it is a topological manifold that is not separable. If time permits, show that it is sequentially compact, but not compact, or show other properties from [this list](https://topology.pi-base.org/spaces/S000038).
  - [general topology] Define some spaces that are typically used for counterexamples, such as the Hawaiian earring, wild knots or the horned sphere, and (dis)prove some topological properties for them.
  - [general topology] Prove Sierpinski's theorem: A nonempty countable metric space without isolated points is homeomorphic to `ℚ`.
  - [general topology] Prove the Sierpinski-Mazurkiewicz theorem: A countable compact Hausdorff space is homeomorphic to an ordinal with the order topology.
  - [algebraic topology] Mathlib has a definition of simplicial complexes. Define oriented simplices and simplicial homology (if useful you can define abstract simplicial complexes yourself and do it for that definition).
  - [algebraic topology] Mathlib has a definition of singular homology: prove that is satisfies the homotopy invariance axiom. (The definition of singular homology uses abstract category theory machinery, so this is more suitable if you have used Lean before.)
  - [algebraic topology] Define n-connected spaces and n-connected maps (by defining the homotopy fiber of a (continuous) map). Prove that for spaces: 0-connected = path connected and 1-connected = simply connected. Try to prove some other easy properties, but beware that many properties are hard, since Mathlib doesn't have homology, Borsuk-Ulam or cellular approximation yet.

## Formalization Tips

Here are some tips for your project.

### Read relevant mathlib files

* There is a rough Mathlib overview here: https://leanprover-community.github.io/mathlib-overview.html
  This can give you an idea what is already in Mathlib.
* Make sure you look through Mathlib what related concepts to your project already exists. It is useful to use https://leansearch.net/ for this
* Look at the related work in more detail in the Mathlib docs:
  https://leanprover-community.github.io/mathlib4_docs/.
  For some results, opening the file in Lean will give you even more information.
* The link above is for the newest version of Mathlib. It is possible that some things have changed slightly since the course started. There is also a version of the documentation pages for the exact version of Mathlib this course uses, here: https://florisvandoorn.com/LeanCourse25/docs/
* Step through some of the proofs in Lean.
  You can open the file locally by going to e.g.
  `LeanCourse25/.lake/packages/mathlib/Mathlib/Algebra/Group/Basic.lean`
  Note that the `.lake` folder is hidden in VSCode sidebar, but you can navigate through it with `ctrl+O` or `cmd+O`.

### Searching

During class I already discussed searching using the name (using autocomplete or the mathlib docs), the statement (using `exact?`, `apply?`, `have?` or `rw??`), using natural language (leansearch)
or precise syntax (loogle).

### Asking for help

* If you have trouble with anything, make sure to ask the tutor or teacher for help during class, the tutorial or the Lean hacking session.
* If you are stuck on something, try replacing it by `sorry` and move on to the next part until you can ask about it.

* You are allowed to ask any AI for help. I do not necessarily recommend using them,
  often their suggestions are not very helpful. If you're using AI, you need to document this (see below).
  * GitHub copilot can sometimes help with stating lemmas or proving a set.
  * ChatGPT knows some Lean, but it can be bad at proofs (and sometimes suggests outdated Lean 3 syntax)


### Writing definitions

It is useful to find a definition that already exists in mathlib and is similar to what you want.
Then you can mimic the structure of that definition.
This can also be useful in deciding whether to use `def`, `structure` or `class`.

## Handing in your project

Projects are due on February 6 (the last week of class). We will publish your (pass/fail) grades for the project by February 13.

To "hand in" your project, you just have to push to your fork of GitHub, and check that all the files show up on GitHub.

Your project should contain a short description of its contents, to help judge what you've formalized.
This should be included in the repository as a pdf or markdown file (not Word or rich text format).
Please answer the following questions:

* What are the main results in your formalization.
* Do you have any `sorry`'s or unfinished proofs? Describe what part (if any) is unfinished.
* What references/sources have you used?
* If you used AI: what tools did you use? How did you use it? Describe what parts of the projects are done by the AI and which parts by you.
