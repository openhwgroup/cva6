"""
This module makes it possible to trigger GitHub workflows.
"""

from os import environ as env
import requests

def api_url(owner, repo):
    "Build API url for a given repository"
    return f"https://api.github.com/repos/{owner}/{repo}"

def pulls(owner, repo):
    "Get (public) pull requests from a given repository"
    url = api_url(owner, repo) + '/pulls'
    headers = {}
    if 'GH_TOKEN' in env:
        headers["Authorization"] = f"Token {env['GH_TOKEN']}"
    response = requests.get(url, headers=headers)
    assert response.status_code == 200
    return response.json()

class Workflow:
    "GitHub Workflow that can be triggered on a dispatch event"
    def __init__(self, owner, repo, workflow_id, ref):
        dispatches = f"/actions/workflows/{workflow_id}/dispatches"
        self.url = api_url(owner, repo) + dispatches
        self.ref = ref

    def _trigger(self, inputs):
        "Trigger the workflow"
        data = {
            'ref': self.ref,
            'inputs': inputs,
        }
        token = env['GH_TOKEN']
        headers = {
            'Accept': 'application/vnd.github+json',
            'Authorization': f"Bearer {token}",
            'X-GitHub-Api-Version': '2022-11-28',
        }
        return requests.post(url=self.url, json=data, headers=headers)

class DashboardDone(Workflow):
    "`dashboard-done.yml` GitHub workflow"
    def __init__(self, owner, repo, ref):
        workflow_id = 'dashboard-done.yml'
        Workflow.__init__(self, owner, repo, workflow_id, ref)

    def send(self, pr, success):
        "Send success or failure message"
        inputs = {
            'pr_number': str(pr),
            'success': success,
        }
        return self._trigger(inputs)

    def send_success(self, pr):
        "Send message stating that job is successful"
        return self.send(pr, True)

    def send_failure(self, pr):
        "Send message stating that job is failed"
        return self.send(pr, False)
