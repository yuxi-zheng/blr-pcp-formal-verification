#!/usr/bin/env python3
"""Benchmark QESAT PCP verifiers and plot runtime growth."""

from __future__ import annotations

import argparse
import csv
import subprocess
from pathlib import Path

import matplotlib.pyplot as plt


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT_DIR = Path(__file__).resolve().parent / "out"
CSV_FIELDS = ["verifier", "vars", "polys", "trials", "accepts", "elapsed_ms", "avg_ms"]


def run(cmd: list[str], *, capture: bool = False) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=capture,
    )


def collect_rows(
    pcp_max_vars: int,
    trivial_max_vars: int,
    trials: int,
    *,
    build: bool,
) -> list[dict[str, str]]:
    if build:
        run(["lake", "build", "qesat_test"])

    exe = REPO_ROOT / ".lake" / "build" / "bin" / "qesat_test"
    result = run(
        [str(exe), "csv", str(pcp_max_vars), str(trials), str(trivial_max_vars)],
        capture=True,
    )
    lines = [line for line in result.stdout.splitlines() if line.strip()]

    try:
        header_index = lines.index(",".join(CSV_FIELDS))
    except ValueError as exc:
        raise RuntimeError("qesat_test did not emit the expected CSV header") from exc

    return list(csv.DictReader(lines[header_index:]))


def write_csv(rows: list[dict[str, str]], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(rows)


def measured_points(rows: list[dict[str, str]], verifier: str) -> list[tuple[int, float]]:
    points = [
        (
            int(row["vars"]),
            max(0.001, int(row["elapsed_ms"]) / max(1, int(row["trials"]))),
        )
        for row in rows
        if row["verifier"] == verifier
    ]
    points.sort()
    return points


def plot_rows(rows: list[dict[str, str]], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    fig, ax = plt.subplots(figsize=(8, 5))
    pcp_points = measured_points(rows, "pcp")
    trivial_points = measured_points(rows, "trivial")

    for verifier, points in [("pcp measured", pcp_points), ("trivial measured", trivial_points)]:
        if not points:
            continue
        xs, ys = zip(*points)
        ax.plot(xs, ys, marker="o", label=verifier)

    ax.set_title("QESAT verifier runtime")
    ax.set_xlabel("variables")
    ax.set_ylabel("average runtime per trial (ms)")
    ax.set_yscale("log")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(path, dpi=180)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--pcp-max-vars",
        type=int,
        default=24,
        help="maximum variable count for the PCP verifier benchmark",
    )
    parser.add_argument(
        "--trivial-max-vars",
        type=int,
        default=20,
        help="maximum variable count for the brute-force verifier benchmark",
    )
    parser.add_argument("--trials", type=int, default=3, help="trials per verifier and size")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR, help="output directory")
    parser.add_argument("--no-build", action="store_true", help="skip `lake build qesat_test`")
    args = parser.parse_args()

    rows = collect_rows(
        args.pcp_max_vars,
        args.trivial_max_vars,
        args.trials,
        build=not args.no_build,
    )
    csv_path = args.out_dir / "qesat.csv"
    png_path = args.out_dir / "qesat_runtime.png"
    write_csv(rows, csv_path)
    plot_rows(rows, png_path)

    print(f"wrote {csv_path}")
    print(f"wrote {png_path}")


if __name__ == "__main__":
    main()
