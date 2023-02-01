# Contributing to the PULP branch

> :warning: When opening a PR, **make sure that `pulp-platform:pulp-vx` is selected as base**, not upstream master.

## General

Wherever possible, follow the upstream [Contribution Guidelines](https://github.com/openhwgroup/cva6/blob/master/CONTRIBUTING.md).
The default goal for all contributions on the PULP branch is that they can be upstreamed eventually.


## Systemlevel modifications

Some contributions have implications on the interfaces of CVA6, or they require the addition of new regression tests.
This fork uses [Cheshire](https://github.com/pulp-platform/cheshire) as a testharness.
We use the following flow for co-development:

1. Branch off the current `pulp-vx` branch (the default branch of this fork) and make your modifications.
   In the following, we refer to your development branch as `cva6/my-feature`.
2. Branch off Cheshire's `main` branch. We will call this new branch `cheshire/my-feature`.
   Point to `cva6/my-feature` in Cheshire's `Bender.lock` and make your systemlevel modifications.
3. In CVA6's `.gitlab-ci.yml`, point the Cheshire ref to `cheshire/my-feature`.
4. Mark your pulp-CVA6 PR ready for review. **The maintainers** will
   - review your modifications to CVA6 and Cheshire,
   - create a tag on `cheshire/my-feature`,
   - merge `cva6/my-feature`,
   - create a new release tag for CVA6 (`pulp-vx.y.z`).
5. Point Cheshire's `Bender.yml` and `Bender.lock` to `pulp-vx.y.z`.
6. Open a PR on the Cheshire repo.

If you have any questions or need support, please contact the maintainers of pulp-CVA6 (see README.md).
