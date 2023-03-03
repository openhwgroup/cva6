# Contributing
New Contributors are always welcome.

Note that Contributors are required to be covered by an [Eclipse Contributor Agreement](https://www.eclipse.org/legal/ECA.php).
Contributors are encouraged, but not required, to be a [member](https://www.openhwgroup.org/membership/) of the OpenHW Group.

## Read this before

### Major evolutions

CVA6 has turned into an industrial project, where the core is being verified to be integrated in production ICs.
In the same time, we'd like to continue integrating new contributions to keep CVA6 a vivid and innovative ecosystem.
But this comes with constraints to ensure that new contributions do not put the industrial project at risk.

Therefore here are guidelines to help the CVA6 team accept new contributions:

- Get in touch early with the CVA6 team, present your initiative, get feedback, synchronize with the team...
    * The CVA6 team wants to assess the potential of your contribution.
    * The CVA6 team can provide you recommendations to ease the upcoming contribution.
    * This can help save significant review and overhauling effort for you and us when dealing with the pull request review.
    * Together, we can anticipate specific cases that are not addressed here.
    * If you do not know how to contact us already, get in touch through info@openhwgroup.org.
    
- Specific recommendations:
    * Always consider using the CV-X-IF interface if your contribution is an instruction-set extension.
        - and talk to the team if it's not possible.
    * Your contribution shall be optional and fully disabled by default.
        - so that projects already using CVA6 are not impacted (no functionality change, no extra silicon...).
    * To configure your contribution, System Verilog top-level parameters are preferred.
        - Synchronize with CVA6 team if this is not possible and you need other means (`directives, ariane_pkg parameters, templating...)
        - Synchronize with CVA6 team (again) because this rule is likely to change over time as we are considering templating.
    * Commit to maintain your contribution 2 years after the pull request
        - We know it's not always possible, so refer to the next rule.
    * Your complete contribution shall be identifiable with parameters (or `directives / templating if together we decide to go this way).
        - If at some point we need to revert it, e.g. if there is no-one maintaining nor using it and it has become a burden to the project.
        - We call this the "parachute" rule: The CVA6 team does not want to use it but is far more comfortable getting one.
    * Your contribution shall pass the Continuous Integration (CI) flow
        - When the contribution is disabled: in all cases, to ensure you have not broken the design.
        - When the contribution is enabled: in relevant cases.
        - You can issue a "do not merge" pull request to test your contribution.
    * Your contribution shall come with its own regression test to integrate in the CI flow.
        - So that we can detect quickly if future updates break your contribution.
        - To avoid impacting those users who use your contribution in their project.
        - At this point, we do not request a 100%-coverage verification suite.

If you encounter difficulties with these guidelines, get in touch with the team!

### Bug fixing

Bug fixing is always welcome. You can issue a GitHub issue. Better: solve the bug and trigger a pull request.

## The Mechanics
1. From GitHub: [fork](https://help.github.com/articles/fork-a-repo/) the [cva6](https://github.com/openhwgroup/cva6) repository
2. Clone repository: `git clone https://github.com/[your_github_username]/cva6`
3. Create your feature branch: `git checkout -b <my_branch>.`<br> Please uniquify your branch name.
See the [Git Cheats](https://github.com/openhwgroup/core-v-verif/blob/master/GitCheats.md) for a useful nomenclature.
4. Make your edits...
5. Commit your changes: `git commit -m 'Add some feature'`
6. Push feature branch: `git push origin <my_branch>`
7. From GitHub: submit a pull request

## Coding Style

For RTL coding, the OpenHW Group has adopted the [lowRISC Style Guides](https://github.com/lowRISC/style-guides/).

## Git Considerations

- Do not push to master, if you want to add a feature do it in your branch.
- Separate subject from body with a blank line.
- Limit the subject line to 50 characters.
- Capitalize the subject line.
- Do not end the subject line with a period.
- Use the imperative mood in the subject line.
- Use the present tense ("Add feature" not "Added feature").
- Wrap the body at 72 characters.
- Use the body to explain what and why vs. how.
- Consider starting the commit message with an applicable emoji:
    * :sparkles: `:sparkles:` When introducing a new feature
    * :art: `:art:` Improving the format/structure of the code
    * :zap: `:zap:` When improving performance
    * :fire: `:fire` Removing code or files.
    * :memo: `:memo:` When writing docs
    * :bug: `:bug:` When fixing a bug
    * :fire: `:fire:` When removing code or files
    * :wastebasket: `:wastebasket:` When removing code or files
    * :green_heart: `:green_heart:` When fixing the CI build
    * :construction_worker: `:construction_worker:` Adding CI build system
    * :white_check_mark: `:white_check_mark:` When adding tests
    * :lock: `:lock:` When dealing with security
    * :arrow_up: `:arrow_up:` When upgrading dependencies
    * :arrow_down: `:arrow_down:` When downgrading dependencies
    * :rotating_light: `:rotating_light:` When removing linter warnings
    * :pencil2: `pencil2:` Fixing typos
    * :recycle: `:scisccor:` Refactoring code.
    * :boom: `:boom:` Introducing breaking changes
    * :truck: `truck` Moving or renaming files.
    * :space_invader: `:space_invader:` When fixing something synthesis related
    * :beers: `:beer:` Writing code drunkenly.
    * :ok_hand: `:ok_hand` Updating code due to code review changes
    * :building_construction: `:building_construction:` Making architectural changes.

For a detailed why and how please refer to one of the multiple [resources](https://chris.beams.io/posts/git-commit/) regarding git commit messages.

If you use `vi` for your commit message, consider to put the following snippet inside your `~/.vimrc`:

```
autocmd Filetype gitcommit setlocal spell textwidth=72s
```
