<!--
Copyright 2023 Thales Silicon Security

Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
You may obtain a copy of the License at https://solderpad.org/licenses/

Original Author: Côme ALLART - Thales
-->

# GitLab CI for core-v-verif + CVA6

This document describes the different steps performed automatically when a branch is pushed to a repository.
It is not meant to be a complete description.
It is an entry point to help to understand the structure of the pipelines; to find the information your are looking for / the part of the CI you want to edit.
Please refer to the mentioned files for more details.

Only the GitLab-related tasks are described here.


## Before the branch reaches GitLab

CVA6 and core-v-verif repositories are mirrored into GitLab repositories owned by Thales, to perform regression tests on pull requests.

> Note: in CVA6 regression tests are also run on the `master` branch, and in core-v-verif on the `cva6/dev` branch.


## Pipeline boot

When a branch is pushed, the entry point of the CI is the `.gitlab-ci.yml` file at the repository root.

> See [`core-v-verif/.gitlab-ci.yml`] and [`cva6/.gitlab-ci.yml`]

[`core-v-verif/.gitlab-ci.yml`]: https://github.com/openhwgroup/core-v-verif/blob/cva6/dev/.gitlab-ci.yml
[`cva6/.gitlab-ci.yml`]: https://github.com/openhwgroup/cva6/blob/master/.gitlab-ci.yml

Both source files from a `setup-ci` project (to locate tools etc.), define workflow rules and perform a small environment check.

All pipelines need both CVA6 and core-v-verif to run tests.
By default the branches used are:

- The one from the PR
- The main branch from the other repository.
  The main branch is defined in `setup-ci` (`master` for CVA6 and `cva6/dev` for core-v-verif).

However, the entry points also detect the `cvvdev/*` pattern in the branch name to run CVA6 and core-v-verif pipelines on branches with the same name.
It is useful to consistently test PRs impacting both repositories.

In the CVA6 pipeline:

1. The `core-v-verif-build` job gets the current commit hash of core-v-verif to set it as an environment variable.
   It gets the list of tests to run [`core-v-verif/.gitlab-ci/cva6.yml`] (see next steps).
2. The `core-v-verif` job triggers a child pipeline using:
   - [`core-v-verif/.gitlab-ci/cva6.yml`] fetched by `core-v-verif-build`
   - [`cva6/.gitlab-ci/core-v-verif-cva6.yml`] which defines a `before_script` and an `after_script` to `cd` the core-v-verif repository with the hash defined by `core-v-verif-build`

[`core-v-verif/.gitlab-ci/cva6.yml`]: https://github.com/openhwgroup/core-v-verif/blob/cva6/dev/.gitlab-ci/cva6.yml
[`cva6/.gitlab-ci/core-v-verif-cva6.yml`]: https://github.com/openhwgroup/cva6/blob/master/.gitlab-ci/core-v-verif-cva6.yml

In core-v-verif pipelines, the `cva6` job triggers a child pipeline using:

- [`core-v-verif/.gitlab-ci/cva6.yml`] (the list of tests)
- [`core-v-verif/.gitlab-ci/core-v-verif-cva6.yml`] (global `before_script` and `after_script`).

[`core-v-verif/.gitlab-ci/core-v-verif-cva6.yml`]: https://github.com/openhwgroup/core-v-verif/blob/cva6/dev/.gitlab-ci/core-v-verif-cva6.yml


## Running the tests

Thanks to the previous step, in pipelines from both CVA6 and core-v-verif, the current working directory is core-v-verif, with CVA6 checked out in `core-v-cores/cva6`.

The tests are described in [`core-v-verif/.gitlab-ci/cva6.yml`].

Stages are defined as below (order matters):

- `init env`: only contains `pub_initjob`, which sets a hash for CVA6 as an environment variable, so that it is the same one for all jobs of this pipeline.
  It is only run in core-v-verif pipelines as CVA6 pipelines already have the CVA6 commit hash of the pipeline!
- `build tools`: `pub_build_tools` build Spike and `pub_check_env` prints some environment variable for debugging.
- `smoke tests`: `pub_smoke` runs smoke tests.
- `verif tests`: many jobs runs different verif tests.
  The template for them is described later in this document.
- `backend tests`: jobs which use results of `verif tests`, often synthesis results.
- `report`: `merge reports` merges all reports into a single yaml.


### Adding a verif test

A simple test looks like this:

```yml
pub_<name>:
  extends:
    - .verif_test
    - .template_job_short_ci
  variables:
    DASHBOARD_JOB_TITLE: "<title for dashboard>"
    DASHBOARD_JOB_DESCRIPTION: "<description for dashboard>"
    DASHBOARD_SORT_INDEX: <index to sort jobs in dashboard>
    DASHBOARD_JOB_CATEGORY: "<job category for dashboard>"
  script:
    - source cva6/regress/<my-script>.sh
    - python3 .gitlab-ci/scripts/report_<kind>.py <args...>
```

- `.verif_test` tells that:
  - The job goes in `verif tests` stage
  - Before running the script part, additionally to the global `before_script`:
    - Spike is got from `pub_build_tools`
    - Artifacts are cleaned, `artifacts/reports` and `artifacts/logs` are created
    - A "failure" report is created by default (in case the script exists early)
    - `$SYN_VCS_BASHRC` is sourced
  - All the contents of the `artifacts/` folder will be considered as artifacts (even if the job fails)
- `.template_job_short_ci` tells in which pipeline mode the job should run
- `variables` defines environment variables.
  The 4 above are needed to generate the report for the dashboard.
- `script` defines the script to run:
  1. Run the test, for instance sourcing a script in `cva6/regress/`
  2. Generate a report running a script from `.gitlab-ci/scripts/reports_*.py`

> Notes:
>
> You can add more environment variables such as:
>
> ```yml
> variables:
>   DV_SIMULATORS: "veri-testharness,spike"
>   DV_TESTLISTS: "../tests/testlist_riscv-tests-$DV_TARGET-p.yaml"
> ```
>
> You can also have several jobs running in parallel with variables taking different values:
>
> ```yml
> parallel:
>   matrix:
>     - DV_TARGET: [cv64a6_imafdc_sv39, cv32a60x]
> ```


### Adding a backend test

```yml
pub_<name>:
  needs:
    - *initjob
    - pub_<other_job>
    - <...>
  extends:
    - .backend_test
    - .template_job_always_manual
  variables:
    <same as for verif tests>
  script:
    - <mv spike from artifacts if you need it>
    - <your script>
    - python3 .gitlab-ci/scripts/report_<kind>.py <args...>
```

Backend tests are like verif tests, differences are:

- `needs` list is needed to specify in which conditions the test is run (with `.template_job_*`).
  It contains:
  - `*initjob` to be sure the correct CVA6 commit is used.
    Without a `needs` list, all jobs from all previous stages are considered as needed.
    However, when a `needs` list is declared, all useful dependencies must be specified by hand, which is more complex.
  - `pub_build_tools` if you need spike (don't forget to `mv` it from the artifacts!)
  - The jobs you need artifacts from
- `.backend_test` indicates that:
  - The job goes in `backend tests` stage
  - It performs the same steps than `.backend_test`, except that:
    - it does not source VCS (so you have to do it if you need it)
    - it does not move spike (so you have to do it if you need it)


## Generating a report

You might want to use `.gitlab-ci/scripts/report_simu.py`.

If it does not suit your needs, below are snippets to help you write a report generator using our python library.

```python
import report_builder as rb

# Create metrics
metric = rb.TableMetric('Metric name')
metric.add_value('colomn 1', 'colomn 2', 'etc')

# Gather them into a report
report = rb.Report('report label')
report.add_metric(metric)

# Create the report file in the artifacts
report.dump()
```

There are 3 kinds of metric:

```python
# A simple table
metric = rb.TableMetric('Metric name, actually not displayed yet')
metric.add_value('colomn 1', 'colomn 2', 'etc')

# A table with a pass/fail label on each line
metric = rb.TableStatusMetric('Metric name, actually not displayed yet')
metric.add_pass('colomn 1', 'colomn 2', 'etc')
metric.add_fail('colomn 1', 'colomn 2', 'etc')

# A log
metric = rb.LogMetric('Metric name, actually not displayed yet')
metric.add_value("one line (no need to add a backslash n)")
metric.values += ["one line (no need to add a backslash n)"] # same as above
metric.values = ["line1", "line2", "etc"] # also works

# You can fail a metric of any kind at any moment
metric.fail()
```

Failures are propagated:

- one fail in a `TableStatusMetric` fails the whole metric
- one failed metric fails the whole report
- one failed report fails the whole pipeline report


## Dashboard

The `merge reports` job merges the report from all jobs of the pipeline into a single file.
It pushes this file to a repository.
This repository has a CI which produces HTML dashboard pages from the latest files.
These HTML pages are published on <https://riscv-ci.pages.thales-invia.fr/dashboard/>

- Main pages [`dashboard_cva6_0.html`] and [`dashboard_core-v-verif_0.html`] gather results from all processed pipelines.
- Each page `dashboard_<project>_<PR id>.html` gathers results from all pipelines of one PR.

[`dashboard_cva6_0.html`]: https://riscv-ci.pages.thales-invia.fr/dashboard/dashboard_cva6_0.html
[`dashboard_core-v-verif_0.html`]: https://riscv-ci.pages.thales-invia.fr/dashboard/dashboard_core-v-verif_0.html


## PR comment

The `merge reports` job gets the list of open PRs.
It compares the name of the current branch with the name of each PR branch to find the PR.
If a PR matches, it triggers the GitHub workflow `dashboard-done.yml` in this repository, providing the PR number and the success/fail status.

> See [`core-v-verif/.github/workflows/dashboard-done.yml`] and [`cva6/.github/workflows/dashboard-done.yml`]

[`core-v-verif/.github/workflows/dashboard-done.yml`]: https://github.com/openhwgroup/core-v-verif/blob/cva6/dev/.github/workflows/dashboard-done.yml
[`cva6/.github/workflows/dashboard-done.yml`]: https://github.com/openhwgroup/cva6/blob/master/.github/workflows/dashboard-done.yml

This GitHub workflow creates a comment in the PR with the success/fail status and a link to the dashboard page.

However, the dashboard page may not be available right at this moment, as page generation, performed later, takes time.
