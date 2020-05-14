# CI: Continuous Integration
Continuous integration of contributions to the OpenHW Group core-v-verif project is central to the unique [work-flow](https://github.com/openhwgroup/core-v-docs/blob/master/verif/Common/OpenHWGroup_WorkFlow.pdf) developed specifically for this project.

## Simulation Verification
The OpenHW Group continuous integration flow for simulation verification is managed by [Metrics CI toolset](https://www.metrics.ca/).

The CI control script is [.gitlab-ci.yml](https://github.com/openhwgroup/core-v-verif/blob/master/.gitlab-ci.yml) which defines which regression is run when a branch is updated.

The configuration file for regressions is [.metrics.json](https://github.com/openhwgroup/core-v-verif/blob/master/.metrics.json).  This file provides Metrics with all the information required to run a named regression.

Thus, `metrics.json` specifies how to run a set of regressions and `.gitlab-ci.yml` determines which of these regressions is run on the commit of a branch.   Both of these files are located at the root of this repository.

Results of CI regressions are visible at the Metrics/OpenHW-Group Regression [Dashboard](https://imperas.metrics.ca/openHW-cv32/dashboard) (login required).

## Formal Verification
Under development.
