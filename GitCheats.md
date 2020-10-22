# Git cheat-sheet.
A few examples to illustrate use of `git` on the command-line.<br><br>
PLEASE READ CAREFULLY the [CONTRIBUTING.md](https://github.com/openhwgroup/core-v-verif/blob/master/CONTRIBUTING.md)
file in this directory.  You MUST follow the specified flow to contribute to this repository.

If you have a suggestion to improve this document please either submit a pull-request, open an issue or email mike@openhwgroup.org.

## Useful Conventions:
1. Place all your working copies in easy-to-find directories.  A suggested
nominclature is:<br>
`$HOME/GitHubRepos/<GitHub_Account>/<Repository/><Branch>`
2. Use unique and easily recognizable names for your branches.  Suggested
nominclatures are:<br>
\<org\>\_\<userid\>_yyyymmdd    (e.g ohw_mike_20191120)
<br>or:<br>
\<org\>\_\<userid\>\_issue\_\<num\> (e.g ohw_mike_issue_239)<br>

**Examples:**
-   /home/mike/GitHubRepos/openhwgroup/core-v-verif/master
-   /data/mike/GitHubRepos/openhwgroup/core-v-verif/ohw_mike_20191204
-   /wrk/greg/GitHubRepos/openhwgroup/cv32e40p/master
-   /home/mike/GitHubRepos/MikeOpenHWGroup/core-v-docs/ohw_mike_issue_123

## Example Use-cases
"$" is the prompt.  "#" is a comment line. ">" is git output to stdout.

### Clone from the head of a Repo's master branch on the command-line.
Note that this is _not_ a typical use-case (work on a branch instead).<br>
Place all your working copies in easy-to-find directory:<br>
e.g. $HOME/GitHubRepos/<GitHub_Account>/\<Repository\>/\<branch\><br>
$ cd $HOME/GitHubRepos/openhwgroup/cv32e40p<br>
$ git clone --recursive https://github.com/openhwgroup/cv32e40p<br>
$ gvim Makefile #...edit file(s)...<br>
$ git commit -m 'Added support for dsim' Makefile <br>
\# First time users might be asked to update their info...<br>
$ git config --global --edit<br>
$ git commit --amend --reset-author<br>

## Make a branch on the command-line and switch to it
$ cd $HOME/GitHubRepos/openhwgroup/cv32e40p<br>
$ git clone --recursive https://github.com/openhwgroup/cv32e40p ohw_mike_20191121<br>
$ git branch ohw_mike_20191121<br>
$ git checkout ohw_mike_20191121<br>
     ...or...<br>
$ git checkout -b ohw_mike_20191121<br>
\# ...edit file(s)...<br>
\# push files back to the branch<br>
$ git status        # check to see what's different<br>
$ git remote -v     # check to ensure remote is the branch you want<br>
$ git commit -m 'Useful commit message'<br>
$ git push --set-upstream origin ohw_mike_20191122<br>

## Clone directly from a branch to a directory named for that branch
$ cd $HOME/GitHubRepos/openhwgroup/cv32e40p<br>
$ git clone --recursive -b ohw_mike_20191122 https://github.com/openhwgroup/cv32e40p ohw_mike_20191122<br>

## Get the short version of the hash of your clone
$ git log --pretty=format:'%h' -n 1

## Sync a branch to the master (same repo)
$ cd $HOME/GitHubRepos/<GitHub_Account>/<Repository/><Branch><br>
$ git checkout master<br>
$ git pull<br>
$ git checkout <Branch><br>
$ git merge master<br>
$ git push --set-upstream origin <Branch><br>

## Sync a forked repo to make it up-to-date with its upstream repo
The following assumes you have previously created a fork of<br>
    https://github.com/openhwgroup/core-v-docs<br>
to<br>
    https://github.com/MikeOpenHWGroup/core-v-docs<br><br>
$ cd GitHubRepos/MikeOpenHWGroup/core-v-docs<br>
$ git clone https://github.com/MikeOpenHWGroup/core-v-docs.git master<br>
$ cd master<br>
$ git remote -v<br>
  \> origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (fetch)<br>
  \> origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (push)<br>
$ git remote add upstream https://github.com/openhwgroup/core-v-docs.git<br>
$ git remote -v<br>
  \> origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (fetch)<br>
  \> origin	https://github.com/MikeOpenHWGroup/core-v-docs.git (push)<br>
  \> upstream	https://github.com/openhwgroup/core-v-docs.git (fetch)<br>
  \> upstream	https://github.com/openhwgroup/core-v-docs.git (push)<br>
$ git fetch upstream<br>
$ git checkout master<br>
$ git merge upstream/master<br>
$ git push --set-upstream origin master<br>


