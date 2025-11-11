# Project 1: contribute a formal conjecture

In your first project, you will contribute to the Formal Conjectures project by creating a new Lean statement of a mathematical research conjecture. There is a list of formalised mathematical conjectures at https://google-deepmind.github.io/formal-conjectures/; your task is to formalise a conjecture which is not yet present in this list.

This should be a relatively small task, and should only require 10-50 lines of code.
You can do this project alone, or in pairs.


### Detailed Instructions

1. Clone the Formal Conjectures repository: https://github.com/google-deepmind/formal-conjectures
  See [`Git.md`](./Git.md) for Git instructions.
2. Choose a conjecture to formalise, and enter it in [this table](https://uni-bonn.sciebo.de/s/MaJYF3Tf36oQy4Q) together with your name.

    Please make sure it is not contained in the Formal Conjectures repository already.
    If the conjecture you want to formalise is already "taken" by a fellow student, please choose another one.
    Here are some sources for a new conjectures. (You are free to choose a different research conjecture.)
    - Wikipedia: https://en.wikipedia.org/wiki/List_of_conjectures, https://en.wikipedia.org/wiki/Category:Conjectures or elsewhere
    - https://www.erdosproblems.com/ (check that it is not yet there)
    - You can see other sources in the Formal Conjectures README: https://github.com/google-deepmind/formal-conjectures?tab=readme-ov-file#contributing
    - Choose one from the Formal Conjectures issue list: https://github.com/google-deepmind/formal-conjectures/issues?q=is%3Aissue+is%3Aopen+no%3Aassignee+label%3A%22new+conjecture%22

    Make sure that it's possible to state your conjecture without having to develop a whole mathematical theory first.

3. Read the Formal Conjectures [README](https://github.com/google-deepmind/formal-conjectures?tab=readme-ov-file#formal-conjectures), especially the sections "How to Contribute", "Some features" and "Style Guidelines".

    The Formal Conjectures repository requires contributors to sign the contributor agreement (see their Contribution page), which requires a Google account.
    Please sign this agreement, or alternatively you have to write a comment when creating your pull request stating that you accept the contribution guidelines.
4. Create a branch for your conjecture.
5. Formalise your conjecture in Lean, following the guidelines from Formal Conjectures.
    Hint: look at other entries in the repository and mimic those.
    - Write a documentation string with an English statement, enclosed by `/-- -/`.
    - You can also add a variant of the statement.
6. **If the previous step was short** (< 10 lines of Lean code, counting only definitions and theorem statements), **formalize a second one**. Create a separate branch/pull request for the second conjecture.
7. **Ask another a tutor or another student to check whether your formalization looks correct**.
8. Commit and push your changes to your own fork of the repository. Then make a pull request with your formal conjecture to the [upstream repository](https://github.com/google-deepmind/formal-conjectures).
9. Add a link to your pull request(s) to [the table](https://uni-bonn.sciebo.de/s/MaJYF3Tf36oQy4Q).
10. After you receive comments on your pull request, incorporate them, and push them to your branch.
11. Repeat step 9 until the pull request is merged.

### Deadlines

* November 20: Create a first version of your conjecture and make a pull request.
* November 27: Incorporate all requested changes from the first review on your pull request.
* December 5 (not strict): Repeatedly incorporate requests by a reviewer until your pull request is merged.
