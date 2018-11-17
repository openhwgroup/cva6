# Styleguides

See [style-guidlines](https://github.com/pulp-platform/style-guidelines)

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
