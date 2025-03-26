import gitlab
import os

def find(branch):
    GITLAB_URL = "https://gitlab.thales-invia.fr"
    CVA6_PROJECT_ID = os.environ["CVA6_PROJECT_ID"]
    CVA6_PROJECT = gitlab.Gitlab(GITLAB_URL, private_token=os.environ["CVA6_TOKEN"]).projects.get(CVA6_PROJECT_ID, lazy=True)
    MONITORED_BRANCHES = ["master", "cv32a60x"]

    monitored_branches_commit_ids = []

    for monitored_branch in MONITORED_BRANCHES:
        monitored_branches_commit_ids.append(get_branch_commits_ids(monitored_branch))
    branch_commits_ids = get_branch_commits_ids(branch)

    for commit_id in branch_commits_ids:
        for i in range(len(MONITORED_BRANCHES)):
            if commit_id in monitored_branches_commit_ids[i]:
                return MONITORED_BRANCHES[i]
    return "master"

def get_branch_commits_ids(branch):
    return set(commit.id for commit in CVA6_PROJECT.commits.list(ref_name=branch, get_all=False, per_page=100))
