#!/usr/bin/env python3
"""Record CI resource use and stop workspace Lean processes under sustained pressure."""
import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import time


def snapshot(workspace):
    memory = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        key, value = line.split(":", 1)
        memory[key] = int(value.split()[0])
    processes = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            name = (proc / "comm").read_text().strip()
            if name not in {"lean", "lake"}:
                continue
            if not (proc / "cwd").resolve().is_relative_to(workspace):
                continue
            status = (proc / "status").read_text().splitlines()
            rss = next((int(line.split()[1]) for line in status if line.startswith("VmRSS:")), 0)
            args = (proc / "cmdline").read_bytes().decode(errors="replace").split("\0")
            source = next((arg for arg in args if arg.endswith(".lean")), None)
            processes.append({"pid": int(proc.name), "name": name, "rss_mib": round(rss / 1024), "source": source})
        except (OSError, ValueError):
            continue
    return {
        "time": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "available_memory_mib": round(memory["MemAvailable"] / 1024),
        "swap_used_mib": round((memory["SwapTotal"] - memory["SwapFree"]) / 1024),
        "swap_free_mib": round(memory["SwapFree"] / 1024),
        "disk_free_mib": round(shutil.disk_usage(workspace).free / 1024**2),
        "load": os.getloadavg(),
        "processes": processes,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--once", action="store_true", help="Print one sample without terminating processes")
    args = parser.parse_args()
    workspace = Path(os.environ.get("GITHUB_WORKSPACE", os.getcwd())).resolve()
    if not args.once and os.environ.get("GITHUB_ACTIONS") != "true":
        parser.error("Continuous monitoring is restricted to GitHub Actions")
    low_samples = 0
    while True:
        data = snapshot(workspace)
        print(json.dumps(data), flush=True)
        if args.once:
            return
        memory_low = data["available_memory_mib"] < 512 and data["swap_free_mib"] < 512
        low = memory_low or data["disk_free_mib"] < 1024
        low_samples = low_samples + 1 if low else 0
        if low_samples >= 2 and data["processes"]:
            print("Stopping workspace Lean processes: sustained memory or disk pressure", flush=True)
            for process in data["processes"]:
                try:
                    proc = Path("/proc") / str(process["pid"])
                    if (proc / "comm").read_text().strip() in {"lean", "lake"} and (proc / "cwd").resolve().is_relative_to(workspace):
                        os.kill(process["pid"], signal.SIGTERM)
                except (OSError, ValueError):
                    pass
            return
        time.sleep(5)


if __name__ == "__main__":
    main()
