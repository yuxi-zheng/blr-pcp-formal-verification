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


def ceil_log2(n: int) -> int:
    if n <= 1:
        return 0
    return (n - 1).bit_length()


def pcp_query_bound_model(vars_count: int) -> int:
    proof_dim = vars_count + vars_count * vars_count
    lpcp_queries = 4
    repetition = ceil_log2(100 * lpcp_queries)
    lpcp_randomness = 1 + 2 * vars_count
    one_conversion = (
        3
        + 2 * repetition * lpcp_queries
        + lpcp_randomness
        + (2 + repetition * lpcp_queries) * proof_dim
    )
    return 6 * one_conversion


def scale_model(
    model: list[tuple[int, float]],
    measured: list[tuple[int, float]],
) -> list[tuple[int, float]]:
    if not model or not measured:
        return []
    measured_x, measured_y = measured[-1]
    anchor = next((y for x, y in model if x == measured_x), model[-1][1])
    if anchor == 0:
        return []
    scale = measured_y / anchor
    return [(x, y * scale) for x, y in model]


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


def plot_rows(rows: list[dict[str, str]], path: Path, model_max_vars: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)

    fig, ax = plt.subplots(figsize=(8, 5))
    pcp_points = measured_points(rows, "pcp")
    trivial_points = measured_points(rows, "trivial")

    for verifier, points in [("pcp measured", pcp_points), ("trivial measured", trivial_points)]:
        if not points:
            continue
        xs, ys = zip(*points)
        ax.plot(xs, ys, marker="o", label=verifier)

    max_vars = max([model_max_vars] + [x for x, _ in pcp_points + trivial_points])
    xs = list(range(1, max_vars + 1))
    pcp_model = [(x, float(pcp_query_bound_model(x))) for x in xs]
    trivial_model = [(x, float(2 ** x)) for x in xs]

    for label, model, measured in [
        ("PCP query-bound model, scaled", pcp_model, pcp_points),
        ("2^n model, scaled", trivial_model, trivial_points),
    ]:
        scaled = scale_model(model, measured)
        if not scaled:
            continue
        model_xs, model_ys = zip(*scaled)
        ax.plot(model_xs, model_ys, linestyle="--", alpha=0.75, label=label)

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
        default=3,
        help="maximum variable count for the PCP verifier benchmark",
    )
    parser.add_argument(
        "--trivial-max-vars",
        type=int,
        default=16,
        help="maximum variable count for the brute-force verifier benchmark",
    )
    parser.add_argument("--trials", type=int, default=3, help="trials per verifier and size")
    parser.add_argument(
        "--model-max-vars",
        type=int,
        default=24,
        help="maximum variable count for scaled asymptotic model curves",
    )
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
    plot_rows(rows, png_path, args.model_max_vars)

    print(f"wrote {csv_path}")
    print(f"wrote {png_path}")


if __name__ == "__main__":
    main()
