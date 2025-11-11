This page will describe some Git terminology and Git actions.

## Git Terminology

* `git` is a version control system. It will store changes you made, and will allow you to revert to previous versions of your files.
* All versions of your files are stored in the `git history`.
* A `commit` is a snapshot of the repository. You have to manually make a commit, and can only refer to the state of the repository at each commit.
* A `branch` is a reference to a commit that can be updated. You usually create a branch to work on one feature.
* Before you commit you can `stage` the files that you want to include in your next commit.
* You have to `push` commits that you make locally on your computer to save them remotely (on `github.com`).
* You can `pull` to download remote commits and get them locally.
* `fetch` is similar to `pull`, but it only downloads the new changes to your git history, but doesn't actually incorporate the changes.
* VSCode uses the word `sync` to mean `pull` + `push`.
* A `fork` is your own remote copy of the repository on `github.com` (something like `github.com/<YourUsername>/LeanCourse25`). You cannot write to the main (upstream) repository (`github.com/fpvandoorn/LeanCourse25`).
* You can request a change by making a `pull request`.
* If two people both make independent commits to a repository, you can `merge` the commits to create a new commit that has both changes.
* If both commits make a change to the same (or adjacent) lines of a file, then you will get a `merge conflict` which means you have to decide how to merge these two changes.
  - *If you get a merge conflict*: this means that you modified the same or adjacent lines as someone else. `git` should tell you which file(s) have a conflict. You can try to `resolve` these conflicts or you can simply choose one version to keep.

## How to...

The following sections describe how to do Git actions from within VS Code. You can also do these actions using commands on a terminal, but I will not describe those in detail here.

Most actions require you to go to the `Source Control` side bar on the left (likely the third button from the top).

### Get started

* Create an account on `github.com`
* On the command line, run the following two commands, with your name and email substituted in. You can open a terminal in VSCode with `` ctrl+` ``/`` cmd+` `` (or with `ctrl+J`/`cmd+J` and clicking `Terminal`)
```
git config --global user.name "Your Name"
git config --global user.email "youremail@yourdomain.com"
```

### Clone

* You have already cloned the `LeanCourse25` repository at the start of this course.
  To clone another Lean repository, the easiest way is to use the `∀` extension menu (top right of this editor) using
  `∀ > Open Project > Download Project...` and typing the repository URL (e.g. `https://github.com/google-deepmind/formal-conjectures`)
* This will also download the corresponding version of Lean and Mathlib.
* It will show a pop-up when it is finished
* Note: if a repository imports files from the same repository, you have to build those files before Lean starts running on a file you open.
  Lean will give a message "Imports are out of date" and then you can press "Restart Files".
  - When it's building, it will show messages of the following form above the import statement.
  ```
  ✔ [nnnn/nnnn] Built FormalConjectures
  ```
  - (This should not build any files from Mathlib. Otherwise, close and reopen VSCode and run `∀ > Project Actions > Fetch Mathlib Build Cache`)

### Pull

*Pulling* allows you to get new changes from a remote repository.

If you have not yet made a fork, do the following:
* Press the three dots next to `Changes` panel and use `⋯ > Pull`.

If you have made a fork, you should instead use:

* Press the three dots next to `Changes` panel and use `⋯ > Pull / Push > Pull from ... > upstream/master`
* (optionally) press `sync changes` to also push your changes.

### Commit and push

The first time you commit and push requires you to *Fork* the repository, if you don't have permission to write to the main repository. VS Code will do this for you, but it requires a few steps:

* Save all your open files
* Write a small commit message (what you write is not important, but it should not be empty). Press `Commit`.
* Press `Yes` (or `Always`) on the prompt `There are no staged changes to commit. Would you like to stage all changes and commit them directly?`. This will also commit changes to all files you changed. Alternatively you can select the files you wish to commit beforehand.
* Press `Sync changes`
* Press `OK` (or `OK, don't show again`) when prompted `This action will pull and push commits from and to "origin/master"`
* In the new window, press `Sign in with browser`
* If needed, sign in to GitHub
* Press `Authorize git-ecosystem`
* You get the message that you don't have permission to push. Press `Create Fork`.
* You should now see your changes at your fork of the repository (e.g. `github.com/<Your GitHub Username>/formal-conjectures`).

Subsequent commits are much easier:

* Save all your open files
* Write a small commit message and press `Commit`.
* Press `Sync changes`

### Branches

Before you make changes, you should create a new branch for your work.

To create a new branch:
* Press the three dots icon next to `Changes` panel and use `⋯ > Branches > Create Branch...` and choose a name for your branch.

To switch between branches:
* Make sure you have saved and committed all your files.
* Press the three dots icon next to `Changes` panel and use `⋯ > Checkout to...` and select the branch you want to switch to.

### Make a pull request

If you recently made pushed changes to a branch of your repository, you can simply go to the
pull request page of the upstream repository (e.g. https://github.com/google-deepmind/formal-conjectures/pulls).
You will see a message there to create a pull request.

Alternatively, you can navigate to your own branch on GitHub and create a pull request there.

Whenever you push new commits while on your branch, your pull request will get updated automatically.
