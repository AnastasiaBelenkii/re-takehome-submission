#!/usr/bin/env python3
"""Launch, monitor, and summarize the seven-run baseline/control deficit wave."""

from __future__ import annotations

import argparse, concurrent.futures, json, os, re, shlex, subprocess, sys, time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

CONFIRMATION = "I_UNDERSTAND_THIS_LAUNCHES_PAID_RUNS"
ROOT = Path(__file__).resolve().parents[1]
RUN_IDS = (
    "qwen-stock-25-r2", "gpt-stock-25-r2", "portfolio-25x2-r2",
    "qwen-stock-50-r1", "qwen-stock-50-r2", "gpt-stock-50-r1", "gpt-stock-50-r2",
)
EXISTING = {"qwen-stock-25": 1, "gpt-stock-25": 1, "portfolio-25x2": 1,
            "qwen-stock-50": 0, "gpt-stock-50": 0}


def now() -> str: return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def parse_assignments(values: list[str]) -> dict[str, str]:
    answer = {}
    for value in values:
        run_id, sep, host = value.partition("=")
        if not sep or run_id not in RUN_IDS or not re.fullmatch(r"[A-Za-z0-9._-]+", host):
            raise ValueError(f"invalid --job {value!r}")
        answer[run_id] = host
    if set(answer) != set(RUN_IDS) or len(set(answer.values())) != 7:
        raise ValueError("provide every run exactly once on seven distinct hosts")
    return answer


def ssh(host: str, remote: str, *, check: bool = True) -> str:
    result = subprocess.run(["ssh", "-o", "BatchMode=yes", host, "bash", "-lc", shlex.quote(remote)],
                            check=check, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return result.stdout


def parse_launch(output: str) -> dict[str, Any]:
    fields = {}
    for line in output.splitlines():
        key, sep, value = line.partition("=")
        if sep and key in {"pid", "commit", "worktree", "run_root", "log", "provenance"}:
            fields[key] = value.strip()
    if not all(fields.get(k) for k in ("pid", "commit", "run_root", "log")):
        raise ValueError("launcher output lacked required fields")
    fields["pid"] = int(fields["pid"])
    return fields


def launch_remote(run_id: str, host: str, commit: str, ref: str) -> str:
    manifest = f"experiments/baseline-controls-2rep-v1/runs/{run_id}.json"
    git_ssh = "ssh -i /root/.ssh/re_takehome_deploy -o IdentitiesOnly=yes -o StrictHostKeyChecking=accept-new"
    commands = ["set -euo pipefail", "cd /root/re-takehome",
                f"GIT_SSH_COMMAND={shlex.quote(git_ssh)} git fetch origin {shlex.quote(ref)}",
                f"git cat-file -e {shlex.quote(commit + '^{commit}')}", f"git switch --detach {commit}",
                f"test \"$(git rev-parse HEAD)\" = {commit}",
                f"python3 scripts/launch_baseline_control.py {manifest} --check",
                f"python3 scripts/launch_baseline_control.py {manifest} --confirm-paid-launch {CONFIRMATION}"]
    return ssh(host, "\n".join(commands))


POLL_CODE = r'''import json, os, pathlib, sys
root=pathlib.Path(sys.argv[1]); pid=int(sys.argv[2])
results=list((root/'outputs').rglob('result.json')) if (root/'outputs').is_dir() else []
runs=list((root/'outputs').rglob('run.json')) if (root/'outputs').is_dir() else []
summaries=list((root/'outputs').rglob('summary.json')) if (root/'outputs').is_dir() else []
finished=False; score=None; statuses={}; cost=0.0
if len(runs)==1 and len(summaries)==1:
 try:
  run=json.loads(runs[0].read_text()); summary=json.loads(summaries[0].read_text())
  finished=bool(run.get('finished_at')) and bool(summary.get('finished_at'))
  entries=summary.get('problems', summary.get('results', []))
  if isinstance(entries, dict): entries=list(entries.values())
  score=sum(1 for e in entries if e.get('status')=='passed')
  for e in entries: statuses[e.get('status','unknown')]=statuses.get(e.get('status','unknown'),0)+1
  cost=sum(float(e.get('cost_usd') or e.get('cost') or 0) for e in entries)
 except Exception: pass
alive=True
try: os.kill(pid,0)
except (ProcessLookupError,PermissionError): alive=False
state='complete' if finished else ('running' if alive else 'exited_incomplete')
print(json.dumps({'state':state,'completed':len(results),'score':score,'statuses':statuses,'cost_usd':cost,'pid_alive':alive}))'''


def poll(host: str, root: str, pid: int) -> dict[str, Any]:
    output = ssh(host, f"python3 -c {shlex.quote(POLL_CODE)} {shlex.quote(root)} {pid}")
    return json.loads(output.strip().splitlines()[-1])


def dashboard(state: dict[str, Any], fleet: list[str]) -> str:
    lines = [f"BASELINE/CONTROL WAVE  updated {state.get('updated_at','?')}", ""]
    total_done = 0
    conditions = dict(EXISTING)
    for run_id in RUN_IDS:
        job = state["jobs"][run_id]; p = job.get("last_poll", {})
        done = int(p.get("completed", 0)); total_done += done
        condition = run_id.rsplit("-r", 1)[0]
        if p.get("state") == "complete": conditions[condition] += 1
        elapsed = max(0, time.time() - job.get("launched_epoch", time.time())) if job.get("launched_epoch") else 0
        if p.get("state") == "complete": eta = "done"
        elif done: eta = f"~{max(0, elapsed * (16-done)/done)/60:.0f}m"
        else: eta = "≤160m"
        lines.append(f"{run_id:23} {job['host']:17} {p.get('state',job.get('launch_state','pending')):17} {done:2}/16  score={str(p.get('score','-')):>2}  ETA {eta}")
    lines += ["", f"new problem results: {total_done}/112",
              "replication totals: " + "  ".join(f"{k}={v}/2" for k,v in conditions.items())]
    assigned = {job["host"] for job in state["jobs"].values()}
    terminal_hosts = {job["host"] for job in state["jobs"].values() if job.get("last_poll",{}).get("state") in {"complete","exited_incomplete"}}
    free = [host for host in fleet if host not in assigned or host in terminal_hosts]
    lines.append("free machines: " + (", ".join(free) if free else "none"))
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", required=True); parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--job", action="append", default=[]); parser.add_argument("--fleet", action="append", default=[])
    parser.add_argument("--remote-ref", default="baseline-controls-2rep-v1")
    parser.add_argument("--confirm-paid-launch"); parser.add_argument("--poll-seconds", type=float, default=30)
    parser.add_argument("--wait-timeout-seconds", type=float, default=14400)
    args = parser.parse_args()
    try:
        if not re.fullmatch(r"[0-9a-f]{40}", args.commit): raise ValueError("commit must be full SHA")
        jobs = parse_assignments(args.job); state_path = args.state.resolve()
        if state_path.exists():
            state=json.loads(state_path.read_text())
            if state.get("commit") != args.commit or state.get("assignments") != jobs: raise ValueError("resume arguments differ")
            is_new=False
        else:
            if args.confirm_paid_launch != CONFIRMATION: raise ValueError("paid-launch confirmation required")
            state={"schema_version":1,"created_at":now(),"updated_at":now(),"commit":args.commit,"assignments":jobs,
                   "phase":"dispatching","jobs":{r:{"host":h,"launch_state":"dispatched_unknown"} for r,h in jobs.items()}}
            atomic(state_path,state); is_new=True
        if is_new:
            def one(item: tuple[str,str]) -> tuple[str,str]:
                rid,host=item
                try: return rid,launch_remote(rid,host,args.commit,args.remote_ref)
                except subprocess.CalledProcessError as exc: return rid,exc.stdout or str(exc)
            with concurrent.futures.ThreadPoolExecutor(max_workers=7) as ex: results=list(ex.map(one,jobs.items()))
            for rid,output in results:
                cell=state["jobs"][rid]; cell["launch_output"]=output[-12000:]
                try:
                    cell.update(parse_launch(output)); cell["launch_state"]="launched"; cell["launched_epoch"]=time.time()
                except Exception as exc: cell["launch_state"]="failed_or_unknown"; cell["launch_error"]=str(exc)
            state["phase"]="monitoring"; state["updated_at"]=now(); atomic(state_path,state)
        if not all(j.get("run_root") and j.get("pid") for j in state["jobs"].values()):
            state["phase"]="manual_intervention_required"; atomic(state_path,state); print(dashboard(state,args.fleet)); return 2
        deadline=time.monotonic()+args.wait_timeout_seconds
        while True:
            active=[(rid,j) for rid,j in state["jobs"].items() if j.get("last_poll",{}).get("state") not in {"complete","exited_incomplete"}]
            if active:
                def one_poll(item):
                    rid,j=item
                    try: return rid,poll(j["host"],j["run_root"],int(j["pid"]))
                    except Exception as exc: return rid,{"state":"poll_error","error":str(exc)}
                with concurrent.futures.ThreadPoolExecutor(max_workers=7) as ex: polled=list(ex.map(one_poll,active))
                for rid,value in polled: state["jobs"][rid]["last_poll"]={**value,"at":now()}
            state["updated_at"]=now(); atomic(state_path,state)
            print("\033[2J\033[H"+dashboard(state,args.fleet),flush=True)
            states=[j.get("last_poll",{}).get("state") for j in state["jobs"].values()]
            if all(s in {"complete","exited_incomplete"} for s in states): break
            if time.monotonic()>=deadline: state["phase"]="monitor_timeout"; atomic(state_path,state); return 3
            time.sleep(args.poll_seconds)
        state["phase"]="complete" if all(s=="complete" for s in states) else "incomplete"
        state["updated_at"]=now(); atomic(state_path,state); return 0 if state["phase"]=="complete" else 4
    except Exception as exc:
        print(f"controller refusal: {exc}",file=sys.stderr); return 1


if __name__ == "__main__": raise SystemExit(main())
