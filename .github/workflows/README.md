# Github CI Regressions
The directory contains YAML files that specify the functional regressions for core-v-verif projects.  The regressions use the Github Actions YAML
to specify and implement regressions.  This README will specify usage and intention of the YAML files in this directory with a brief introduction to 
the YAML.  For more documentation on Github YAML refer to: https://docs.github.com/en/actions

Two general types of regressions are specified:
| Type       | Starting Event | Goal           |
|:-----------|:---------------|:---------------|
| Triggered  | Push on an official core-v-verif branch | Ensure that merges occur properly and testbench on official branches are in a working state.  Should be largely immune from RTL instability | 
| Scheduled  | On regularly scheduled times | Larger regressions to measure testbench implementation, coverage, and RTL stability.  It expected these regressions will show failing tests while under development. |

## Naming Convention

All regressions specified in these regression YAMLs should have the following convention to ensure consistency:

*core*\_*regression*\_*branch*

Examples
- A ci_check that executes on the _dev_ branch of the cv32e40p (cv32e40p/dev) should be named: _cv32e40p_ci_check_dev_
- A release check (rel_check) that executes on the _master_ branch for the cv32e40x should be named: _cv32e40x_rel_check_master_

## Metrics
All regressions will be executed using the Metrics cloud simulation platform https://metrics.ca/

Contributors to core-v-verif who are affiliated with OpenHW Members can request an account with access to the OpenHW core-v-verif project to review
details on regression results including pass/fail, coverage, trends, etc.

https://openhwgroup.metrics.ca/main-core-v-verif-openhwgroup/dashboard

The Metrics regressions are specified in .metrics.json in the root directory of core-v-verif.  Note that all Github CI regressions must have an entry in the .metrics.json file for proper
trend analysis.

## Triggered Regressions

The file triggered-metrics-regress.yml contains definitions of all regressions that start upon push to one of the "official branches" for core-v-verif

- master
For each core in development (e.g. cv32e40p, cv32e40x)
- _core_/dev
- _core_/dev

The triggered YAML workflow is started when any of the in-development branches are pushed to:

```
on:
  push:
    branches:
      - master
      - cv32e40p/dev
      - cv32e40p/release
```

Individual jobs in each yaml should only execute when the intended branch is pushed using full git refs format:

```
  cv32e40p_ci_check_dev-metrics:    
    runs-on: ubuntu-latest    
    if: github.ref == 'refs/heads/cv32e40p/dev'
    steps:
      - uses: actions/checkout@v2
        with:
          ref: cv32e40p/dev
      - run: ./bin/metrics-regress $METRICS_REGRESSION_NAME $METRICS_PROJECT_ID
        env:
          METRICS_CI_TOKEN: ${{ secrets.METRICS_CI_TOKEN }}
          METRICS_REGRESSION_NAME: cv32e40p_ci_check_dev
          METRICS_PROJECT_ID: ${{ secrets.METRICS_PROJECT_ID }}
          PR_NUMBER: ${{ github.event.pull_request.number }}
        shell: bash
```

## Scheduled

Scheduled regressions should be specified on a per-core basis using *core*-scheduled-metrics-regress.yml.  Scheduled regressions should target the dev branch for the core intended.
The only other major difference from a triggered regression is that a branch trigger specification is replaced by a cron-like specification.  https://docs.github.com/en/actions/reference/events-that-trigger-workflows#scheduled-events

```
on:
  schedule:
    # This will run nightly (in the Western Hemisphere) at 0500 UTC
    - cron: '0 5 * * *'
```



