# Contribution Guidelines

If you find bugs or have questions or feature requests, please discuss the issue the maintainer of
the respective IP block (see header of the source file).  All developers are encouraged to
contribute small, simple patches that can be reviewed easily.  If your patch is too large, break it
into logically connected, atomic units.  A best-practice contribution follows this sequence:

1.  Add a test to the testbench that clearly specifies the bug or feature you want to tackle.  As
    you have not contributed your code yet, this test must fail.  Have it do so with a descriptive
    reason.

2.  Write the code that meets your specifications, thus causes the test to pass.  The code does not
    yet have to be perfect, as it will be improved later.

3.  Run all tests in this repository and make sure they *all* pass.  Do *not* modify any tests other
    than the one you added for this contribution.

4.  Reach back to the maintainer to discuss specifications and code.  If your code initially caused
    any other tests to fail and you had to modify existing code to get them to pass again, mention
    this.

5.  Refactor your code to make it clean, simple, and maintainable.  Repeat steps 3 to 5 until no
    refactoring is necessary anymore.  Ask the maintainer to merge your contribution.

We only accept contributions that follow the formatting conventions specified by the
[`.editorconfig`](./.editorconfig) file.  If you use an editor that is suitable for editing code,
chances are good that it can automatically take care of this (either out of the box or with a
plugin, see http://editorconfig.org for more information).
