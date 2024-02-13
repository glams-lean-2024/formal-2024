# Formalising Mathematics in Lean

This is the repository for the GlaMS course on Formalising Mathematics in Lean. The course content (workshop sheets and homeworks) is located in the folder `Formal2024`. There is also a `References` folder.

## How to work on this

### Starting the repository

#### In Codespaces/Gitpod
The easy method: Use Lean in your very own web browser! <br>
This can be done using Codespaces:<br> [![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/glams-lean-2024/formal-2024?quickstart=1) <br>
Or using Gitpod:<br> [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/glams-lean-2024/formal-2024)

#### Locally
Installing Lean on your computer following these [instructions](https://leanprover-community.github.io/get_started.html).
Then you can clone this repository to your own computer by writing `git clone https://github.com/glams-lean-2024/formal-2024.git` in your terminal, followed by `lake exe cache get`.

---
### Working on the repository

All the files we will be using can be found in the folder Formal2024: this contains both the workshop and homework sheets.

In order to work on this efficiently, please make a copy of the folder and working on the copy rather than in the folder Formal2024. You can do this by writing `cp -r Formal2024 MyFiles` in your terminal. This copies the whole folder into a new folder called "MyFiles" which you will be working on (you can even create your own Lean files in that folder to experiment on!).

Each week, when the repository gets updated, you can type `git pull` in your terminal, followed by `lake exe cache get`. This adds the new files into the folder `Formal2024`, which you can then copy manually into your own folder.

If you do work on the Formal2024 folder, and get a merge conflict when pulling the repository, then you should type `git config pull --rebase false` before `git pull`, you probably would need to also `git add --all` and `git commit -m "some message"` before `git pull` if you do get a merge conflict.

---
### Troubleshooting in Codespaces/Gitpod

- after waiting ~5 minutes for the codespaces to run, you will want to restart any opened file (by doing ctrl / command + shift + P, then you search for something along the lines of `Lean4:restart file`)
- if it still doesn't work, then you `lake exe cache get` in your terminal
- if it still doesn't work, then you `lake update` in your terminal
- if you're still not progressing, please message on Discord `#general` under the `Lean` category

