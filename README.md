# Bonn Lean Course WiSe 25/26

## In this repository

You will find the Lean files in the `LeanCourse25` directory:
* The `Lectures` folder contains all lectures (we will post 2 versions of each lecture file: one before class, and one after class with the comments we wrote during class)
* The `Assignments` folder contains the assignments that you have to hand in via eCampus.
<!-- * The `MIL` folder contains the exercises from the book Mathematics in Lean. You can find the textbook online here:
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
(or as a
[pdf document](https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf)). -->

## Installation

* These [instructions](https://docs.lean-lang.org/lean4/doc/quickstart.html) will guide you through the installation process.

* This will guide you to install VSCode (a text editor which supports Lean) and Lean.

* As part of the **extension setup**, in the step **Set up Lean 4 project** click on **Download an existing project**, if prompted choose `Git repository URL`, and enter `https://github.com/fpvandoorn/LeanCourse25` as the URL. Then navigate to the directory where you want to download this repository, and specify a folder name. It will create a new directory with that name for you. This will download Mathlib, which will take a few minutes.

* When you have downloaded the repository a message appears allowing you to open the project folder.
To test that everything is working, open the repository and open the file `LeanCourse25/Test.lean`.
The file should be ready after loading a while. If you see a blue squiggle under `#eval`, Lean is running correctly.

* A useful (but optional) extension is the VSCode extension `Error Lens`. If you install this, you will see messages from Lean right in the file where you're typing.

## Troubleshooting

Note: To get this repository, you will need to download Lean's mathematical library, which takes about 5 GB of storage space.

It might be tricky to get Lean running on a laptop that is more than 10 years old or on a chromebook, since Lean does use a moderate amount of recourses.
You can still run Lean in your browser by using Codespaces or Gitpod, see the the instructions at the bottom of this file.

* On Windows, antivirus programs can cause slowdowns or errors when downloading a Lean project. Consider temporarily disabling your antivirus program in the step *Complete the extension setup*

* If you get errors such as `curl: (35) schannel` or `uncaught exception: no such file or directory (error code: 2)` take a look [here](https://leanprover-community.github.io/install/project.html#troubleshooting).

* If after installing the extension, you see 5 steps, but nothing else: please close all side panels (and possibly decrease the font size). For some reason the second (important) column is hidden if there is not enough room.

* Unfortunately, the installation step, and loading Lean for the first time is very slow on Windows computers. Once Lean has finished starting up, it should be quick and responsive.

## Update repository

If you want to get the latest version of this repository (e.g. the latest exercises), then you can pull the changes.

You can do this either via a terminal (`git pull`)
or via VSCode, in the `Source Control` tab (third icon in the top-left, or `ctrl+shift+G`/`cmd+shift+G`),
under `⋯` (More actions) you can click `Pull` to get the latest changes.

Note: you should *not* press `Sync`, since that will try to upload your changes to the assignment files to GitHub (you don't have the rights to do this).

Note: you should not need to build mathlib files on your computer. If you notice, try the following steps:
* Close VSCode (if it is open).
* Open the course folder in VS Code and open some Lean file in the course.
* Press `∀ > Project Actions... > Fetch Mathlib Build Cache` and wait for the cache to download.
* Wait until the command finishes with downloading and decompressing. If you get an error, run it again.
* You might have to restart the Lean file, and then Lean should be compiling your file in less than a minute.

<!-- We might at some point update the version of Lean for the repository (we will tell you when this happens). In that case, after running `git pull` you have to get the new Mathlib cache. In this case, *do not* restart a Lean file (which will prompt Lean to rebuild Mathlib on your laptop).
Instead press `∀ > Project Actions... > Fetch Mathlib Build Cache` and wait for the cache to download.
After it has finished, you might have to restart the Lean file, and then Lean should be compiling your file in less than a minute. -->

<!-- If this fails, try the following steps:
* Close VSCode (if it is open)
* In your terminal, in the `LeanCourse25` folder, run `lake exe cache get!` (or `~/.elan/bin/lake exe cache get!` if `lake` cannot be found).
* Wait until the command finishes with downloading and decompressing. If you get an error, run it again.
* Now you can reopen VSCode and restart the file (if prompted). -->

## Temporary ways to use Lean

You can temporarily use Codespaces or Gitpod if you have trouble installing Lean locally.

### Using Codespaces

You can temporarily play with Lean using GitHub codespaces. This requires a GitHub account, and you can only use it for a limited amount of time each month. If you are signed in to GitHub, click here:

<a href='https://codespaces.new/fpvandoorn/LeanCourse25' target="_blank" rel="noreferrer noopener"><img src='https://github.com/codespaces/badge.svg' alt='Open in GitHub Codespaces' style='max-width: 100%;'></a>

* Make sure the Machine type is `4-core`, and then press `Create codespace`
* After 1-2 minutes you see a VSCode window in your browser. However, it is still busily downloading mathlib in the background, so give it another few minutes (5 to be safe) and then open a `.lean` file to start.

### Using Ona

Ona (formerly Gitpod) is an alternative to codespaces that is a bit inconvenient, since it requires you to verify your phone number.

Click this button to get started:

[![Open in Ona](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/fpvandoorn/LeanCourse25)

This creates a virtual machine in the cloud,
and installs Lean and Mathlib.
It then presents you with a VS Code window, running in a virtual
copy of the repository.
You can update the repository by opening a terminal in the browser
and typing `git pull` followed by `lake exe cache get!` as above.

<!-- Ona gives you 50 free hours every month.
When you are done working, choose `Stop workspace` from the menu on the left.
The workspace should also stop automatically
30 minutes after the last interaction or 3 minutes after closing the tab. -->

<!-- To restart a previous workspace, go to [https://gitpod.io/workspaces/](https://gitpod.io/workspaces/). -->

### Live Browser version

You can run a single Lean online in the [Live editor](https://live.lean-lang.org/#project=mathlib-stable). If you haven't managed to install Lean yet, you can use this to work on a single file (e.g. an exercise file) by copy-pasting the contents in the online editor.

Warning: this could lead to subtle errors, because the live editor might use a slightly different version of Lean and Mathlib.

## Links

* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
* [Lean website](https://www.lean-lang.org/)
* [Lean-community website](https://leanprover-community.github.io/)
* [Topics in Mathlib](https://leanprover-community.github.io/mathlib-overview.html)
* [API documentation for this course](https://florisvandoorn.com/LeanCourse25/docs/)
* [latest Mathlib API documentation](https://leanprover-community.github.io/mathlib4_docs/)

Some exciting projects using Lean:

* Interesting finished Lean projects: [Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid), [Equational Theories project](https://teorth.github.io/equational_theories/), [Carleson's theorem](https://florisvandoorn.com/carleson/).
* Interesting ongoing Lean projects: [Fermat's Last Theorem](https://imperialcollegelondon.github.io/FLT/)
