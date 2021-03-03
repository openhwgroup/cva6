# Contributing
New Contributors are always welcome. Start by having a look at the **README**,
especially the [getting started](https://github.com/openhwgroup/core-v-verif#getting-started)
section.

## Contributor Agreement
Most Contributors are [members](https://www.openhwgroup.org/membership/) of the
OpenHW Group and participate in one or more [Technical Task Groups](https://www.openhwgroup.org/working-groups/).
Membership is strongly encouraged, but not required.  Contributors must be
covered by the terms of the [Eclipse Contributor Agreement](https://www.eclipse.org/legal/ECA.php)
(for individuals) **or** the [Eclipse Member Committer and Contributor Agreement](https://www.eclipse.org/legal/committer_process/EclipseMemberCommitterAgreement.pdf)
(for employees of Member companies). The ECA/MCCA provides a legal
framework for a Contributor's technical contributions to the OpenHW Group,
including provisions for grant of copyright license and a Developer
Certificate of Origin on contributions merged into OpenHW Group repositories.
<br><br>
All pull-requests to OpenHW Group git repositories must be signed-off using the
`--signoff` (or `-s`) option to the git commit command (see below).

## The Mechanics
1. [Fork](https://help.github.com/articles/fork-a-repo/) the [core-v-verif](https://github.com/openhwgroup/core-v-verif) repository
2. Clone repository: `git clone https://github.com/[your_github_username]/core-v-verif`
3. Create your feature branch: `git checkout -b <my_branch>.`<br> Please uniquify your branch name.  See the [Git Cheats](https://github.com/openhwgroup/core-v-verif/blob/master/GitCheats.md) for a useful nominclature.
4. Test your changes with the [ci_check](https://github.com/openhwgroup/core-v-verif/blob/bin/ci_check) script.
5. Commit your changes: `git commit -m 'Add some feature' --signoff`<br>...take note of that **--signoff**, it's important!
6. Push feature branch: `git push origin <my_branch>`
7. Submit a [pull request](https://help.github.com/en/github/collaborating-with-issues-and-pull-requests/creating-a-pull-request-from-a-fork).
