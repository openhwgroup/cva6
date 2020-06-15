# CI: Continuous Integration
Continuous integration of contributions to the OpenHW Group core-v-verif project is central to the unique [work-flow](https://github.com/openhwgroup/core-v-docs/blob/master/verif/Common/OpenHWGroup_WorkFlow.pdf) developed specifically for this project.  When you submit a pull-request to either this repository or one of the core RTL repositories (such as [cv32e40p](https://github.com/openhwgroup/cv32e40p)) it will be subjected to a full CI regression.  The definition of what a "full CI
regression" will change over time and is specified by various CI scripts (see below).

## User-level Regression
To maximize the liklihood of a clean outcome for a pull-request, you can run a user-level regression using `ci_check` (in this
directory).  This script runs a sub-set of the tests defined in the simulation CI regression scripts.  If your pull-request passes the ci_check, it is considered safe to merge into a branch of the [core-v-verif](https://github.com/openhwgroup/core-v-verif)
repository.
<br><br>
The command `./ci_check -h` should tell you everything you need to know to run
a user-level regression.  Note that the script has the ability to specify the
URL, branch and hash of the RTL to be regressed (usually this is picked up in
`../cv32/sim/Common.mk`.  An example command is:
<br>
`./ci_check -s xrun --repo https://github.com/MikeOpenHWGroup/cv32e40p --branch dev1 --hash=12345` 
<br>
If ci_check is not working for you, create an issue and assign it to @mikeopenhwgroup.
<br><br>
At the completion of ci_check the script will print a message to stdout indicating whether it is OK to issue a pull-request based on the outcome of the regression.  Note that some of the tests in a regression may have known failuresi and the script will
compensate for them. A typical example is:
```
CI Check PASSED with known failure(s).
OK to issue a pull-request.
```

## Simulation CI Regressions
The OpenHW Group continuous integration flow for simulation verification is managed by the [Metrics CI toolset](https://www.metrics.ca/).
<br>
The CI control script is [.gitlab-ci.yml](https://github.com/openhwgroup/core-v-verif/blob/master/.gitlab-ci.yml) which defines which regression is run when a branch is updated.
<br>
The configuration file for regressions is [.metrics.json](https://github.com/openhwgroup/core-v-verif/blob/master/.metrics.json).  This file provides Metrics with all the information required to run a named regression.
<br>
Thus, `metrics.json` specifies how to run a set of regressions and `.gitlab-ci.yml` determines which of these regressions is run on the commit of a branch.   Both of these files are located at the root of this repository.
<br>
Results of CI regressions are visible at the Metrics/OpenHW-Group Regression [Dashboard](https://imperas.metrics.ca/openHW-cv32/dashboard) (login required).

## Formal CI Regressions
Under development.
