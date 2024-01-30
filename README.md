# Formalising Mathematics in Lean

This is the repository for the GlaMS course on Formalising Mathematics in Lean. The course content (workshop sheets and homeworks) is located in the folder `Formal2024`. There is also a `References` folder.

## How to work on this

1. The easy method: Use Lean in your very own web browser! <br>
   This can be done using Codespaces:<br> [![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/glams-lean-2024/formal-2024?quickstart=1) <br>
   Or using Gitpod:<br> [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/glams-lean-2024/formal-2024)

### Troubleshooting in Codespaces/Gitpod

- after waiting ~5 minutes for the codespaces to run, you will want to restart any opened file (by doing ctrl / command + shift + P, then you search for somethin along the lines of `Lean4:restart file`)
- if it still doesn't work, then you `lake exe cache get` in your terminal
- if it still doesn't work, then you `lake make` in your terminal

3. Installing Lean on your computer following these [instructions](https://leanprover-community.github.io/get_started.html).
   Then you can clone this repository to your own computer by writing `git clone https://github.com/glams-lean-2024/formal-2024.git` in your terminal, followed by `lake exe cache get`.

