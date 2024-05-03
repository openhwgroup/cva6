#!/usr/bin/env bash

# Setup the git hooks
echo "Setting up git-hooks"
echo "===================="

echo "Launched from" $(pwd)
echo ""

echo "Setting up pre-commit"
ln -s -f ../../.git_hooks/pre-commit ./.git/hooks/pre-commit
chmod a+x ./.git/hooks/pre-commit
echo "Done"
