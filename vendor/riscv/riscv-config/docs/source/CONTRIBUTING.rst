.. See LICENSE.incore for details

.. highlight:: shell

============
Contributing
============

Contributions are welcome, and they are greatly appreciated and credit will always be given.

You can contribute in many ways:

Types of Contributions
----------------------

Report Bugs
~~~~~~~~~~~

Report bugs at https://github.com/riscv-software-src/riscv-config/issues/ .

Submit Feedback
~~~~~~~~~~~~~~~

The best way to send feedback is to file an issue at https://github.com/riscv-software-src/riscv-config/issues/.

If you are proposing a feature:

* Explain in detail how it would work.
* Keep the scope as narrow as possible, to make it easier to implement.
* Remember that this is a volunteer-driven project, and that contributions
  are welcome :)

Get Started!
------------

Ready to contribute? Here's how to set up `riscv_config` for local development.

1. Fork the `riscv_config` repo on GitHub.
2. Clone your fork locally::

    $ git clone  https://github.com/riscv-software-src/riscv-config.git

3. Create an issue and WIP merge request that creates a working branch for you::

    $ git checkout -b name-of-your-bugfix-or-feature

   Now you can make your changes locally.


5. Commit your changes and push your branch to GitLab::

    $ git add .
    $ git commit -m "Your detailed description of your changes."
    $ git push origin name-of-your-bugfix-or-feature

6. Submit a merge request through the GitHub website.


Versioning
----------

When issuing pull requests, an entry in the CHANGELOG.md is mandatory. The tool adheres to
the [`Semantic Versioning`](https://semver.org/spec/v2.0.0.html) scheme. Following guidelines must
be followed while assigning a new version number :

- Patch-updates: all doc updates (like typos, more clarification,etc).
- Minor-updates: Fixing bugs in current features, adding new features which do not break current
  features or working. Adding new extensions.
- Major-updates: Backward incompatible changes.

Note: You can have either a patch or minor or major update.
Note: In case of a conflict, the maintainers will decide the final version to be assigned.

To update the version of the python package for deployment you can use `bumpversion` (installed
using ``pip install bumpversion``)::

$ bumpversion --no-tag --config-file setup.cfg patch # last arg can be: major or minor or patch

If you don't have bumpversion installed you can manually update the version in the following files:

- change the value of variable ``current_version`` in `./setup.cfg`
- change the value of variable ``__version__`` in `./riscv-config/__init__.py`


Merge Request Guidelines
----------------------------

Before you submit a merge request, check that it meets these guidelines:

1. The merge request should include tests (if any).
2. If the merge request adds functionality, the docs should be updated. 

