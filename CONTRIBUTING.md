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

## Branches
The core-v-verif repository provides testbenches for multiple OpenHW cores.  As such the core-v-verif repository uses branches for maintaining stability between 
the different core testbenches as well as recognizing independent development streams.  An adapted form of the Git Flow is used in this repository.  

The following are the official branches for core-v-verif
 Branch                | Example (if applicable) | Usage               
 --------------------- | ----------------------- | -----------------------
_\<core>_/dev          | cv32e40p/dev            | Main line of development for a core testbench.  Most contributinos should target a dev branch.
_\<core>_/release      | cv32e40p/release        | Staging branch for merge dev branches into master (and vice versa).  In general only OpenHW Committers will utilize these branches
master                 | master                  | Releaseable stable testbench branch.  Can only be updated by OpenHW committer merges or via hotfix PR.  All official releases will reference a commit on the master branch.

In most cases a contribution should be made on a _dev_ branch.<br>
Common infrastructure fixes and updates may target the _master_ branch using the hotfix flow to directly address issues requiring timely fixes.<br>

More information on core-v-verif branch usage can be found here:
https://github.com/openhwgroup/core-v-docs/blob/master/verif/Common/Presentations/20210311-Branches%20and%20CIs%20for%20core-v-verif.pptx

## The Mechanics
1. [Fork](https://help.github.com/articles/fork-a-repo/) the [core-v-verif](https://github.com/openhwgroup/core-v-verif) repository
2. Clone repository: `git clone https://github.com/[your_github_username]/core-v-verif`
3. Checkout the correct branch reflecting the nature of your contribution.  Nearly all contributions should target a core's _dev_ branch.  Hotfixes can target _master_.
4. Create your feature branch: `git checkout -b <my_branch>.`<br> Please uniquify your branch name.  See the [Git Cheats](https://github.com/openhwgroup/core-v-verif/blob/master/GitCheats.md) for a useful nominclature.
5. Test your changes with the [ci_check](https://github.com/openhwgroup/core-v-verif/blob/master/bin/ci_check) script.
6. Commit your changes: `git commit -m 'Add some feature' --signoff`<br>...take note of that **--signoff**, it's important!
7. Push feature branch: `git push origin <my_branch>`
8. Submit a [pull request](https://help.github.com/en/github/collaborating-with-issues-and-pull-requests/creating-a-pull-request-from-a-fork).
9. If known, it is advisable to select one or more appropriate reviewers for your PR.  For hotfix PRs, request either Steve Richmond or Mike Thompson for proper review.