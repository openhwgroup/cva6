# Contributing
New Contributors are always welecome.  Contributors are encouraged, but not required, to be a [member](https://www.openhwgroup.org/membership/) of the OpenHW Group. Have a look at [README](https://github.com/openhwgroup/core-v-verif/blob/master/README.md), especially the [getting started](https://github.com/openhwgroup/core-v-verif#getting-started) section.

## Contributor Agreement
Contributors must be covered by the terms of the [Eclipse Contributor Agreement](https://www.eclipse.org/legal/ECA.php) (for individuals) or the [Eclipse Member Committer and Contributor Agreement](https://www.eclipse.org/legal/committer_process/EclipseMemberCommitterAgreement.pdf) (for employees of Member companies). The ECA/MCCA is an agreement covering a Contributor's role in making technical contributions to the OpenHW Group, and it provides the legal framework for granting copyright on code and/or documents merged into OpenHW Group repositories.
<br>
All pull-requests to OpenHW Group git repositories must be signed-off using the `--signoff` (or `-s`) option to the git commit command (see below).

## The Mechanics
1. [Fork](https://help.github.com/articles/fork-a-repo/) the [core-v-verif](https://github.com/openhwgroup/core-v-verif) repository
2. Clone repository: `git clone https://github.com/[your_github_username]/core-v-verif`
3. Create your feature branch: `git checkout -b <my_branch>.`<br> Please uniquify your branch name.  See the [Git Cheats](https://github.com/openhwgroup/core-v-verif/blob/master/GitCheats.md) for a useful nominclature.
4. Test your changes with the [ci_check](https://github.com/openhwgroup/core-v-verif/blob/regression_test/ci/ci_check) script.
5. Commit your changes: `git commit -m 'Add some feature' --signoff`<br>...take note of that **--signoff**, it's important!
6. Push feature branch: `git push origin <my_branch>`
7. Submit a [pull request](https://help.github.com/en/github/collaborating-with-issues-and-pull-requests/creating-a-pull-request-from-a-fork).
