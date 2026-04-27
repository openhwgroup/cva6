#!/usr/bin/env python3
# Copyright 2026 OpenHW Group
# SPDX-License-Identifier: Apache-2.0
"""Collect CI run/job data from GitHub API for the CVA6 tier dashboard.

Uses `gh api` (pre-installed on GHA runners, auto-authenticated).
Produces per-workflow JSON files with incremental updates.
"""

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from parser import parse_job_name

# Workflows to track
WORKFLOWS = {
    "ci": "ci.yml",
    "tier1": "openhw-cva6-ci-tier1.yml",
    "tier2": "openhw-cva6-ci-tier2.yml",
}

MAX_HISTORY = 50


def gh_api(endpoint: str, repo: str) -> dict:
    """Call GitHub API via `gh api` and return parsed JSON."""
    url = f"/repos/{repo}/actions/{endpoint}"
    result = subprocess.run(
        ["gh", "api", url, "--paginate"],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"ERROR: gh api {url} failed: {result.stderr}", file=sys.stderr)
        sys.exit(1)
    return json.loads(result.stdout)


def gh_api_list(endpoint: str, repo: str, per_page: int = 100) -> dict:
    """Call GitHub API with per_page parameter."""
    url = f"/repos/{repo}/actions/{endpoint}"
    sep = "&" if "?" in url else "?"
    result = subprocess.run(
        ["gh", "api", f"{url}{sep}per_page={per_page}"],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"ERROR: gh api {url} failed: {result.stderr}", file=sys.stderr)
        sys.exit(1)
    return json.loads(result.stdout)


def fetch_runs(repo: str, workflow_file: str, count: int) -> list:
    """Fetch the latest `count` completed workflow runs."""
    data = gh_api_list(
        f"workflows/{workflow_file}/runs?status=completed&per_page={count}",
        repo,
    )
    runs = data.get("workflow_runs", [])
    return runs[:count]


def fetch_jobs(repo: str, run_id: int) -> list:
    """Fetch all jobs for a given workflow run."""
    data = gh_api(f"runs/{run_id}/jobs", repo)
    return data.get("jobs", [])


def duration_seconds(started_at: str, completed_at: str) -> int:
    """Calculate duration in seconds between two ISO timestamps."""
    if not started_at or not completed_at:
        return 0
    try:
        start = datetime.fromisoformat(started_at.replace("Z", "+00:00"))
        end = datetime.fromisoformat(completed_at.replace("Z", "+00:00"))
        return max(0, int((end - start).total_seconds()))
    except (ValueError, TypeError):
        return 0


def process_run(repo: str, run: dict, workflow_name: str) -> dict:
    """Process a single workflow run into our data format."""
    run_id = run["id"]
    jobs_raw = fetch_jobs(repo, run_id)

    jobs = []
    total_jobs = 0
    passed_jobs = 0
    failed_jobs = 0

    for job in jobs_raw:
        parsed = parse_job_name(job["name"], workflow_name)
        if parsed is None:
            continue  # Skip utility jobs

        total_jobs += 1
        conclusion = job.get("conclusion", "unknown")
        if conclusion == "success":
            passed_jobs += 1
        elif conclusion in ("failure", "timed_out"):
            failed_jobs += 1

        job_data = {
            "name": job["name"],
            "conclusion": conclusion,
            "started_at": job.get("started_at", ""),
            "completed_at": job.get("completed_at", ""),
            "duration_seconds": duration_seconds(
                job.get("started_at", ""), job.get("completed_at", "")
            ),
            "html_url": job.get("html_url", ""),
        }
        job_data.update(parsed)
        jobs.append(job_data)

    # Calculate run-level duration
    run_duration = duration_seconds(
        run.get("run_started_at", run.get("created_at", "")),
        run.get("updated_at", ""),
    )

    return {
        "id": run_id,
        "source": "github-actions",  # Extensibility: "questa-aws", "gitlab-ci", etc.
        "simulator": "verilator",    # Extensibility: "questa", "vcs", etc.
        "run_number": run.get("run_number", 0),
        "status": run.get("status", ""),
        "conclusion": run.get("conclusion", "unknown"),
        "html_url": run.get("html_url", ""),
        "head_branch": run.get("head_branch", ""),
        "head_sha": run.get("head_sha", "")[:8],
        "event": run.get("event", ""),
        "created_at": run.get("created_at", ""),
        "updated_at": run.get("updated_at", ""),
        "run_started_at": run.get("run_started_at", run.get("created_at", "")),
        "duration_seconds": run_duration,
        "total_jobs": total_jobs,
        "passed_jobs": passed_jobs,
        "failed_jobs": failed_jobs,
        "skipped_jobs": total_jobs - passed_jobs - failed_jobs,
        "jobs": jobs,
    }


def load_existing(path: Path) -> list:
    """Load existing run data from JSON file."""
    if path.exists():
        try:
            with open(path) as f:
                return json.load(f)
        except (json.JSONDecodeError, IOError):
            print(f"WARNING: Could not read {path}, starting fresh", file=sys.stderr)
    return []


def merge_runs(existing: list, new_runs: list) -> list:
    """Merge new runs into existing data, deduplicating by run_id."""
    existing_ids = {r["id"] for r in existing}
    merged = list(existing)

    for run in new_runs:
        if run["id"] not in existing_ids:
            merged.append(run)
            existing_ids.add(run["id"])

    # Sort by created_at descending (newest first)
    merged.sort(key=lambda r: r.get("created_at", ""), reverse=True)

    # Trim to MAX_HISTORY
    return merged[:MAX_HISTORY]


def main():
    parser = argparse.ArgumentParser(description="Collect CVA6 tier CI data from GitHub API")
    parser.add_argument(
        "--repo",
        default=os.environ.get("GITHUB_REPOSITORY", "openhwgroup/cva6"),
        help="GitHub repository (owner/name)",
    )
    parser.add_argument(
        "--data-dir",
        default="data",
        help="Directory to store JSON data files",
    )
    parser.add_argument(
        "--fetch-count",
        type=int,
        default=10,
        help="Number of recent runs to fetch per workflow",
    )
    args = parser.parse_args()

    data_dir = Path(args.data_dir)
    data_dir.mkdir(parents=True, exist_ok=True)

    for wf_name, wf_file in WORKFLOWS.items():
        print(f"\n{'='*60}")
        print(f"Processing workflow: {wf_name} ({wf_file})")
        print(f"{'='*60}")

        json_path = data_dir / f"runs_{wf_name}.json"
        existing = load_existing(json_path)
        existing_ids = {r["id"] for r in existing}

        print(f"  Existing records: {len(existing)}")

        # Fetch latest runs
        runs = fetch_runs(args.repo, wf_file, args.fetch_count)
        print(f"  Fetched {len(runs)} runs from API")

        # Only process new runs (incremental update)
        new_runs = []
        for run in runs:
            if run["id"] in existing_ids:
                print(f"  Skipping run #{run['run_number']} (id={run['id']}) - already exists")
                continue

            print(f"  Processing run #{run['run_number']} (id={run['id']})...")
            processed = process_run(args.repo, run, wf_name)
            new_runs.append(processed)
            print(
                f"    -> {processed['total_jobs']} jobs: "
                f"{processed['passed_jobs']} passed, "
                f"{processed['failed_jobs']} failed"
            )

        # Merge and save
        merged = merge_runs(existing, new_runs)
        with open(json_path, "w") as f:
            json.dump(merged, f, indent=2)

        print(f"  Saved {len(merged)} records to {json_path}")

    # Write metadata
    meta = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "repo": args.repo,
        "workflows": list(WORKFLOWS.keys()),
    }
    with open(data_dir / "metadata.json", "w") as f:
        json.dump(meta, f, indent=2)

    print(f"\nDone! Data saved to {data_dir}/")


if __name__ == "__main__":
    main()
