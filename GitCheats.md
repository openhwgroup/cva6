# Mini Git cheat-sheet.


PLEASE READ CAREFULLY the "CONTRIBUTING.md" file in this directory.
You MUST follow the specified flow to contribute to this repository.

Useful Conventions:
1. Place all your working copies in easy-to-find directories.  A suggested
nominclature is:<br><br>
`$HOME/GitHubRepos/<GitHub_Account>/<Repository/><Branch>`
2. Use unique and easily recognizable names for your branches.  Suggested
nominclatures are:<br><br>
<org>_<userid>_yyyymmdd    (e.g ohw_mike_20191120)<br>
or:<br>
<org>_<userid>_issue_<num> (e.g ohw_mike_issue_239)<br>
Examples:
<br>   /home/mike/GitHubRepos/openhwgroup/core-v-verif/master
<br>   /home/mike/GitHubRepos/openhwgroup/core-v-verif/ohw_mike_20191204
<br>   /home/mike/GitHubRepos/openhwgroup/cv32e40p/master
<br>   /home/mike/GitHubRepos/MikeOpenHWGroup/core-v-docs/ohw_mike_issue_123

## Example Use-cases
Written as a set of use-cases.  "$" is the prompt.  "//" is a comment line.

### Clone from the head of a Repo's master branch on the command-line.
Note that this is _not_ a typical use-case (work on a branch instead).
Place all your working copies in easy-to-find directory:
e.g. $HOME/GitHubRepos/<GitHub_Account>/<Repository>/<branch>
$ cd $HOME/GitHubRepos/openhwgroup/cv32e40p
$ git clone --recursive https://github.com/openhwgroup/cv32e40p
$ gvim Makefile #...edit file(s)...
$ git commit -m 'Added support for dsim' Makefile 
// First time users might be asked to update their info...
$ git config --global --edit
$ git commit --amend --reset-author

## Make a branch on the command-line and switch to it
$ cd $HOME/GitHubRepos/openhwgroup/cv32e40p
$ git clone --recursive https://github.com/openhwgroup/cv32e40p ohw_mike_20191121
$ git branch ohw_mike_20191121
$ git checkout ohw_mike_20191121
     ...or...
$ git checkout -b ohw_mike_20191121
// ...edit file(s)...
// push files back to the branch
$ git status        # check to see what's different
$ git remote -v     # check to ensure remote is the branch you want
$ git commit -m 'Useful commit message'
$ git push --set-upstream origin ohw_mike_20191122

## Clone directly from a branch to a directory named for that branch
$ cd $HOME/GitHubRepos/openhwgroup/cv32e40p
$ git clone --recursive -b ohw_mike_20191122 https://github.com/openhwgroup/cv32e40p ohw_mike_20191122

## Sync a branch to the master (same repo)
$ cd $HOME/GitHubRepos/<GitHub_Account>/<Repository/><Branch>
$ git checkout master
$ git pull
$ git checkout <Branch>
$ git merge master
$ git push --set-upstream origin <Branch>

##Sync a forked repo to make it up-to-date with its upstream repo
The following assumes you have previously created a fork of
    https://github.com/openhwgroup/core-v-docs
to
    https://github.com/MikeOpenHWGroup/core-v-docs
$ cd GitHubRepos/MikeOpenHWGroup/core-v-docs
$ git clone https://github.com/MikeOpenHWGroup/core-v-docs.git master
$ cd master
$ git remote -v
  > origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (fetch)
  > origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (push)
$ git remote add upstream https://github.com/openhwgroup/core-v-docs.git
$ git remote -v
  > origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (fetch)
  > origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (push)
  > upstream	https://github.com/openhwgroup/core-v-docs.git (fetch)
  > upstream	https://github.com/openhwgroup/core-v-docs.git (push)
$ git fetch upstream
$ git checkout master
$ git merge upstream/master
$ git push --set-upstream origin master

## Merging from a branch onto the master (not confident in this yet)
$ git fetch origin
$ git checkout -b mike_20191202 origin/mike_20191202
$ git merge master
$ git checkout master
$ git merge --no-ff mike_20191202 
$ git push origin master

