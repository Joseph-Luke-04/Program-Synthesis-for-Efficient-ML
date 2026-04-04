from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any, Callable

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
from matplotlib.lines import Line2D


def _parse_hp_benchmark(key: str) -> dict[str, str]:
    if key.endswith("_sub"):
        variant = "Subcomponents"
        base = key[:-4]
    elif key.endswith("_v1"):
        variant = "V1"
        base = key[:-3]
    else:
        variant = "V2"
        base = key

    dtype = "FP32" if base.startswith("fp32") else "MXINT8"
    op = "Addition" if base.endswith("add") else "Multiplication"
    short = f"{dtype} {op}"
    return {
        "benchmark_base": base,
        "dtype": dtype,
        "op": op,
        "variant": variant,
        "benchmark_label": f"{short} ({variant})",
        "display_label": f"{dtype}\n{op}\n{variant}",
    }


def _valid_nonneg(x: Any) -> bool:
    return pd.notna(x) and float(x) >= 0


def _valid_pos(x: Any) -> bool:
    return pd.notna(x) and float(x) > 0


def _dominates(a: dict[str, Any], b: dict[str, Any]) -> bool:
    no_worse = (
        float(a["mean_within_rel_pct"]) >= float(b["mean_within_rel_pct"])
        and float(a["mean_luts"]) <= float(b["mean_luts"])
        and float(a["mean_latency_ns"]) <= float(b["mean_latency_ns"])
        and float(a["mean_adp"]) <= float(b["mean_adp"])
    )
    strictly_better = (
        float(a["mean_within_rel_pct"]) > float(b["mean_within_rel_pct"])
        or float(a["mean_luts"]) < float(b["mean_luts"])
        or float(a["mean_latency_ns"]) < float(b["mean_latency_ns"])
        or float(a["mean_adp"]) < float(b["mean_adp"])
    )
    return no_worse and strictly_better


def _show(display_fn: Callable[[Any], Any] | None, obj: Any) -> None:
    if display_fn is not None:
        display_fn(obj)
    else:
        print(obj)


def run_hyperparameter_sweep_notebook_analysis(
    ROOT: Path,
    display_fn: Callable[[Any], Any] | None = None,
    hp_output_dir: str = "",
    pipeline_df: pd.DataFrame | None = None,
    solve_rate_thresh: float = 1 / 3,
    accuracy_slack_pct_points: float = 0.01,
) -> dict[str, Any]:
    hp_root = ROOT / "results" / "hyperparameter_sweep"

    level1 = list(hp_root.glob("*/runs.jsonl"))
    level2 = list(hp_root.glob("*/*/runs.jsonl"))

    level2_groups: dict[Path, list[Path]] = defaultdict(list)
    for path in level2:
        level2_groups[path.parent.parent].append(path)

    candidates: list[tuple[float, str, list[Path]]] = []
    for path in level1:
        candidates.append((path.stat().st_mtime, path.parent.name, [path]))
    for parent, files in level2_groups.items():
        mtime = max(path.stat().st_mtime for path in files)
        candidates.append((mtime, parent.name, sorted(files)))
    candidates.sort(key=lambda x: x[0], reverse=True)

    if hp_output_dir:
        override_dir = ROOT / hp_output_dir
        override_single = override_dir / "runs.jsonl"
        override_multi = list(override_dir.glob("*/runs.jsonl"))
        if override_single.exists():
            candidates.insert(0, (override_single.stat().st_mtime, hp_output_dir, [override_single]))
        elif override_multi:
            mtime = max(path.stat().st_mtime for path in override_multi)
            candidates.insert(0, (mtime, hp_output_dir, sorted(override_multi)))

    if not candidates:
        raise FileNotFoundError("No hyperparameter sweep results found.")

    best_mtime, best_label, hp_files = candidates[0]
    hp_dir = hp_files[0].parent if len(hp_files) == 1 else hp_files[0].parent.parent

    hp_rows: list[dict[str, Any]] = []
    for path in hp_files:
        for line in path.read_text().splitlines():
            if line.strip():
                hp_rows.append(json.loads(line))

    print(f"Loaded {len(hp_rows)} raw runs from '{best_label}' ({len(hp_files)} file(s))")
    print(f"Source of truth: {hp_dir / 'runs.jsonl' if len(hp_files) == 1 else hp_dir}")
    if len(hp_files) > 1:
        counts: dict[str, int] = defaultdict(int)
        for row in hp_rows:
            counts[row["benchmark"]] += 1
        print("Benchmarks loaded:", dict(sorted(counts.items())))

    summary_csv = hp_dir / "summary.csv"
    if summary_csv.exists() and summary_csv.stat().st_mtime < max(path.stat().st_mtime for path in hp_files):
        print("[Note] summary.csv is older than runs.jsonl; recomputing notebook analysis from raw runs.")

    hp_df = pd.DataFrame(hp_rows)
    if hp_df.empty:
        raise ValueError(f"No rows found in hyperparameter sweep output: {hp_dir}")

    bmeta = hp_df["benchmark"].map(_parse_hp_benchmark).apply(pd.Series)
    hp_df = pd.concat([hp_df, bmeta], axis=1)

    numeric_cols = [
        "timeout",
        "num_iterations",
        "repetition",
        "accepted_constraints",
        "total_constraints",
        "wall_seconds",
        "solver_runtime_seconds_total",
        "within_rel_pct",
        "accuracy_exact_match",
        "luts",
        "ffs",
        "dsps",
        "fmax_mhz",
        "latency_ns",
        "adp_lut_ns",
        "abs_err_avg",
        "abs_err_max",
    ]
    for col in numeric_cols:
        if col in hp_df.columns:
            hp_df[col] = pd.to_numeric(hp_df[col], errors="coerce")

    for col in [
        "within_rel_pct",
        "accuracy_exact_match",
        "luts",
        "fmax_mhz",
        "latency_ns",
        "adp_lut_ns",
        "abs_err_avg",
        "abs_err_max",
    ]:
        if col in hp_df.columns:
            hp_df.loc[hp_df[col] < 0, col] = np.nan

    if "solution_found" not in hp_df.columns:
        hp_df["solution_found"] = hp_df.get("run_status", pd.Series(index=hp_df.index, dtype=object)).eq("solved")
    else:
        hp_df["solution_found"] = hp_df["solution_found"].fillna(False).astype(bool)

    has_accuracy = "within_rel_pct" in hp_df.columns and hp_df["within_rel_pct"].notna().any()
    has_exact = "accuracy_exact_match" in hp_df.columns and hp_df["accuracy_exact_match"].notna().any()
    has_luts = "luts" in hp_df.columns and hp_df["luts"].notna().any()
    has_latency = "latency_ns" in hp_df.columns and hp_df["latency_ns"].notna().any()
    has_adp = "adp_lut_ns" in hp_df.columns and hp_df["adp_lut_ns"].notna().any()
    print(
        f"Metrics present -> within-threshold: {has_accuracy} | exact: {has_exact} | "
        f"LUTs: {has_luts} | latency: {has_latency} | ADP: {has_adp}"
    )

    hp_timeouts = sorted(int(x) for x in hp_df["timeout"].dropna().unique())
    hp_iters = sorted(int(x) for x in hp_df["num_iterations"].dropna().unique())
    hp_reps = sorted(int(x) for x in hp_df["repetition"].dropna().unique()) if "repetition" in hp_df.columns else [1]
    hp_benchmarks = sorted(hp_df["benchmark"].dropna().unique())
    expected_per_point = len(hp_reps)
    expected_per_benchmark = len(hp_timeouts) * len(hp_iters) * expected_per_point
    expected_total = len(hp_benchmarks) * expected_per_benchmark

    completed_by_bench = hp_df.groupby("benchmark").size().rename("completed_runs")
    completeness_rows = []
    for bench in hp_benchmarks:
        meta = _parse_hp_benchmark(bench)
        done = int(completed_by_bench.get(bench, 0))
        completeness_rows.append(
            {
                "Benchmark": meta["benchmark_label"],
                "Completed": done,
                "Expected": expected_per_benchmark,
                "Completion %": 100.0 * done / expected_per_benchmark if expected_per_benchmark else np.nan,
                "Missing Runs": expected_per_benchmark - done,
            }
        )
    hp_completeness_df = pd.DataFrame(completeness_rows)

    print(
        f"Grid audit: {len(hp_benchmarks)} benchmarks x {len(hp_timeouts)} timeouts x "
        f"{len(hp_iters)} iteration counts x {expected_per_point} reps = {expected_total} expected runs"
    )
    print(f"Completed: {len(hp_df)} / {expected_total} ({100.0 * len(hp_df) / expected_total:.1f}%)")
    _show(display_fn, hp_completeness_df)

    missing_rows = []
    for bench in hp_benchmarks:
        meta = _parse_hp_benchmark(bench)
        seen = hp_df[hp_df["benchmark"] == bench].groupby(["timeout", "num_iterations"]).size().to_dict()
        for timeout in hp_timeouts:
            for num_iter in hp_iters:
                count = int(seen.get((timeout, num_iter), 0))
                if count != expected_per_point:
                    missing_rows.append(
                        {
                            "Benchmark": meta["benchmark_label"],
                            "Timeout (s)": timeout,
                            "Iterations": num_iter,
                            "Completed Reps": count,
                            "Expected Reps": expected_per_point,
                            "Missing Reps": expected_per_point - count,
                        }
                    )
    hp_missing_df = pd.DataFrame(missing_rows)
    if not hp_missing_df.empty:
        print("Incomplete sweep points detected:")
        _show(display_fn, hp_missing_df.sort_values(["Benchmark", "Timeout (s)", "Iterations"]).reset_index(drop=True))

    agg_rows = []
    for (bench, timeout, num_iter), gdf in hp_df.groupby(["benchmark", "timeout", "num_iterations"]):
        meta = _parse_hp_benchmark(bench)
        agg_rows.append(
            {
                **meta,
                "benchmark": bench,
                "timeout": int(timeout),
                "num_iterations": int(num_iter),
                "runs_completed": int(len(gdf)),
                "runs_expected": int(expected_per_point),
                "solve_rate": float(gdf["solution_found"].mean()),
                "mean_accepted": float(gdf["accepted_constraints"].mean()) if "accepted_constraints" in gdf.columns else np.nan,
                "mean_wall": float(gdf["wall_seconds"].mean()) if "wall_seconds" in gdf.columns else np.nan,
                "mean_within_rel_pct": float(gdf["within_rel_pct"].mean()) if has_accuracy else np.nan,
                "std_within_rel_pct": float(gdf["within_rel_pct"].std(ddof=0)) if has_accuracy else np.nan,
                "mean_accuracy_exact_match": float(gdf["accuracy_exact_match"].mean()) if has_exact else np.nan,
                "std_accuracy_exact_match": float(gdf["accuracy_exact_match"].std(ddof=0)) if has_exact else np.nan,
                "mean_luts": float(gdf["luts"].mean()) if has_luts else np.nan,
                "mean_ffs": float(gdf["ffs"].mean()) if "ffs" in gdf.columns and gdf["ffs"].notna().any() else np.nan,
                "mean_dsps": float(gdf["dsps"].mean()) if "dsps" in gdf.columns and gdf["dsps"].notna().any() else np.nan,
                "mean_fmax_mhz": float(gdf["fmax_mhz"].mean())
                if "fmax_mhz" in gdf.columns and gdf["fmax_mhz"].notna().any()
                else np.nan,
                "mean_latency_ns": float(gdf["latency_ns"].mean()) if has_latency else np.nan,
                "mean_adp": float(gdf["adp_lut_ns"].mean()) if has_adp else np.nan,
            }
        )

    agg = pd.DataFrame(agg_rows)
    if agg.empty:
        raise ValueError("No aggregated hyperparameter sweep rows could be constructed.")

    def _is_candidate(row: pd.Series) -> bool:
        return (
            _valid_nonneg(row.get("mean_within_rel_pct"))
            and _valid_pos(row.get("mean_luts"))
            and _valid_pos(row.get("mean_latency_ns"))
            and _valid_pos(row.get("mean_adp"))
            and float(row.get("solve_rate", 0.0)) >= solve_rate_thresh
        )

    agg["is_candidate"] = agg.apply(_is_candidate, axis=1)
    agg["is_pareto"] = False
    agg["is_recommended"] = False
    agg["selection_reason"] = ""

    for bench in sorted(agg["benchmark"].unique()):
        mask = agg["benchmark"] == bench
        rows = agg[mask].copy()
        candidates = rows[rows["is_candidate"]].copy()
        if candidates.empty:
            candidates = rows.dropna(
                subset=["mean_within_rel_pct", "mean_luts", "mean_latency_ns", "mean_adp"]
            ).copy()
        if candidates.empty:
            continue

        candidate_records = candidates.to_dict("records")
        for row in candidate_records:
            if not any(_dominates(other, row) for other in candidate_records if other is not row):
                agg.loc[
                    mask
                    & (agg["timeout"] == row["timeout"])
                    & (agg["num_iterations"] == row["num_iterations"]),
                    "is_pareto",
                ] = True

        pareto = agg[mask & agg["is_pareto"]].copy()
        if pareto.empty:
            continue

        best_acc = float(pareto["mean_within_rel_pct"].max())
        near_best = pareto[pareto["mean_within_rel_pct"] >= (best_acc - accuracy_slack_pct_points)].copy()
        pool = near_best if not near_best.empty else pareto
        chosen = pool.sort_values(["mean_adp", "mean_latency_ns", "mean_luts", "mean_wall"], na_position="last").iloc[0]
        agg.loc[
            mask & (agg["timeout"] == chosen["timeout"]) & (agg["num_iterations"] == chosen["num_iterations"]),
            ["is_recommended", "selection_reason"],
        ] = [
            True,
            f"Pareto-optimal; within {accuracy_slack_pct_points * 100:.1f} ppt of best accuracy; minimum ADP among remaining points",
        ]

    for bench in agg["benchmark"].unique():
        bench_mask = agg["benchmark"] == bench
        best_adp = agg.loc[bench_mask, "mean_adp"].dropna().min()
        if pd.notna(best_adp) and best_adp > 0:
            agg.loc[bench_mask, "adp_norm_to_best"] = agg.loc[bench_mask, "mean_adp"] / best_adp
        else:
            agg.loc[bench_mask, "adp_norm_to_best"] = np.nan

    variant_order = {"Subcomponents": 0, "V1": 1, "V2": 2}
    hp_recommended = agg[agg["is_recommended"]].copy()
    hp_recommended["variant_order"] = hp_recommended["variant"].map(variant_order).fillna(99)
    hp_recommended = hp_recommended.sort_values(["dtype", "op", "variant_order"]).drop(columns="variant_order")

    recommended_table = hp_recommended[
        [
            "benchmark_label",
            "dtype",
            "op",
            "variant",
            "timeout",
            "num_iterations",
            "solve_rate",
            "runs_completed",
            "mean_within_rel_pct",
            "mean_accuracy_exact_match",
            "mean_luts",
            "mean_ffs",
            "mean_latency_ns",
            "mean_adp",
        ]
    ].rename(
        columns={
            "benchmark_label": "Benchmark",
            "timeout": "Recommended Timeout (s)",
            "num_iterations": "Recommended Iterations",
            "solve_rate": "Solve Rate",
            "runs_completed": "Reps Completed",
            "mean_within_rel_pct": "Mean Accuracy (5%)",
            "mean_accuracy_exact_match": "Mean Exact Match",
            "mean_luts": "Mean LUTs",
            "mean_ffs": "Mean FFs",
            "mean_latency_ns": "Mean Latency (ns)",
            "mean_adp": "Mean ADP (LUT*ns)",
        }
    ).copy()

    if pipeline_df is not None and not recommended_table.empty and "Mean Exact Match" in recommended_table.columns:
        pipe = pipeline_df.copy()
        if {"dtype", "op", "variant", "exact_pct"}.issubset(pipe.columns):
            pipe_lookup = (
                pipe.dropna(subset=["dtype", "op", "variant"])
                .drop_duplicates(subset=["dtype", "op", "variant"], keep="last")
                .set_index(["dtype", "op", "variant"])["exact_pct"]
                .to_dict()
            )
            for idx, row in recommended_table.iterrows():
                if pd.notna(row["Mean Exact Match"]):
                    continue
                key = (row["dtype"], row["op"], row["variant"])
                if key in pipe_lookup and pd.notna(pipe_lookup[key]):
                    # Pipeline exact_pct is already stored in percentage units;
                    # convert back to fraction so the table formatting logic below
                    # remains consistent with sweep-native values.
                    recommended_table.at[idx, "Mean Exact Match"] = float(pipe_lookup[key]) / 100.0

    recommended_table = recommended_table.drop(columns=["dtype", "op", "variant"], errors="ignore")

    if not recommended_table.empty:
        for col in ["Mean Accuracy (5%)", "Mean Exact Match", "Solve Rate"]:
            if col in recommended_table.columns:
                recommended_table[col] = recommended_table[col] * 100
        recommended_table = recommended_table.round(
            {
                "Solve Rate": 1,
                "Mean Accuracy (5%)": 1,
                "Mean Exact Match": 1,
                "Mean LUTs": 2,
                "Mean FFs": 2,
                "Mean Latency (ns)": 3,
                "Mean ADP (LUT*ns)": 2,
            }
        )

    print("Recommended hyperparameter point per benchmark (Pareto-aware selection)")
    _show(display_fn, recommended_table)

    recommended_latex = recommended_table.copy()
    for col in ["Solve Rate", "Mean Accuracy (5%)", "Mean Exact Match"]:
        if col in recommended_latex.columns:
            recommended_latex[col] = recommended_latex[col].map(lambda x: f"{x:.1f}\\%" if pd.notna(x) else "NaN")
    for col in ["Mean LUTs", "Mean FFs", "Mean Latency (ns)", "Mean ADP (LUT*ns)"]:
        if col in recommended_latex.columns:
            recommended_latex[col] = recommended_latex[col].map(lambda x: f"{x:.2f}" if pd.notna(x) else "NaN")

    print("LaTeX recommended table:")
    print(recommended_latex.to_latex(index=False, escape=False))

    best_baseline_rows: list[dict[str, Any]] = []
    for _, row in hp_recommended.iterrows():
        exact_pct = row.get("mean_accuracy_exact_match")
        if pd.notna(exact_pct):
            exact_pct = float(exact_pct) * 100.0
        elif pipeline_df is not None:
            pipe_match = pipeline_df[
                (pipeline_df.get("dtype") == row["dtype"])
                & (pipeline_df.get("op") == row["op"])
                & (pipeline_df.get("variant") == row["variant"])
            ]
            if not pipe_match.empty and pd.notna(pipe_match.iloc[-1].get("exact_pct")):
                exact_pct = float(pipe_match.iloc[-1]["exact_pct"])
            else:
                exact_pct = np.nan
        else:
            exact_pct = np.nan

        best_baseline_rows.append(
            {
                "dtype": row["dtype"],
                "op": row["op"],
                "variant": row["variant"],
                "status": "BEST",
                "timeout": int(row["timeout"]),
                "num_iterations": int(row["num_iterations"]),
                "LUTs": float(row["mean_luts"]) if pd.notna(row["mean_luts"]) else np.nan,
                "FFs": float(row["mean_ffs"]) if pd.notna(row["mean_ffs"]) else np.nan,
                "DSPs": float(row["mean_dsps"]) if pd.notna(row["mean_dsps"]) else np.nan,
                "Fmax_MHz": float(row["mean_fmax_mhz"]) if pd.notna(row["mean_fmax_mhz"]) else np.nan,
                "Latency_ns": float(row["mean_latency_ns"]) if pd.notna(row["mean_latency_ns"]) else np.nan,
                "ADP": float(row["mean_adp"]) if pd.notna(row["mean_adp"]) else np.nan,
                "within5pct": float(row["mean_within_rel_pct"]) * 100.0 if pd.notna(row["mean_within_rel_pct"]) else np.nan,
                "exact_pct": exact_pct,
            }
        )

    if pipeline_df is not None and {"dtype", "op", "variant", "LUTs", "Latency_ns", "within5pct", "exact_pct"}.issubset(
        pipeline_df.columns
    ):
        flopoco_rows = pipeline_df[pipeline_df["variant"] == "FloPoCo"].copy()
        for _, row in flopoco_rows.iterrows():
            best_baseline_rows.append(
                {
                    "dtype": row["dtype"],
                    "op": row["op"],
                    "variant": "FloPoCo",
                    "status": row.get("status", "SKIP"),
                    "timeout": np.nan,
                    "num_iterations": np.nan,
                    "LUTs": float(row["LUTs"]) if pd.notna(row["LUTs"]) else np.nan,
                    "FFs": float(row["FFs"]) if pd.notna(row.get("FFs")) else np.nan,
                    "DSPs": float(row["DSPs"]) if pd.notna(row.get("DSPs")) else np.nan,
                    "Fmax_MHz": float(row["Fmax_MHz"]) if pd.notna(row.get("Fmax_MHz")) else np.nan,
                    "Latency_ns": float(row["Latency_ns"]) if pd.notna(row["Latency_ns"]) else np.nan,
                    "ADP": (
                        float(row["LUTs"]) * float(row["Latency_ns"])
                        if pd.notna(row["LUTs"]) and pd.notna(row["Latency_ns"])
                        else np.nan
                    ),
                    "within5pct": float(row["within5pct"]) if pd.notna(row["within5pct"]) else np.nan,
                    "exact_pct": float(row["exact_pct"]) if pd.notna(row["exact_pct"]) else np.nan,
                }
            )

    best_baseline_df = pd.DataFrame(best_baseline_rows)
    flopoco_table = pd.DataFrame()
    flopoco_latex = ""
    if not best_baseline_df.empty:
        variant_order_all = {"Subcomponents": 0, "V1": 1, "V2": 2, "FloPoCo": 3}
        op_order = {"Addition": 0, "Multiplication": 1}
        dtype_order = {"FP32": 0, "MXINT8": 1}
        best_baseline_df["dtype_order"] = best_baseline_df["dtype"].map(dtype_order).fillna(99)
        best_baseline_df["op_order"] = best_baseline_df["op"].map(op_order).fillna(99)
        best_baseline_df["variant_order"] = best_baseline_df["variant"].map(variant_order_all).fillna(99)
        best_baseline_df = best_baseline_df.sort_values(
            ["dtype_order", "op_order", "variant_order"]
        ).drop(columns=["dtype_order", "op_order", "variant_order"])

        print("Best baseline comparison from recommended hyperparameter points")
        for dtype in ["FP32", "MXINT8"]:
            dtype_df = best_baseline_df[best_baseline_df["dtype"] == dtype].copy()
            if dtype_df.empty:
                continue
            out = dtype_df[
                [
                    "op",
                    "variant",
                    "status",
                    "timeout",
                    "num_iterations",
                    "LUTs",
                    "FFs",
                    "DSPs",
                    "Fmax_MHz",
                    "Latency_ns",
                    "ADP",
                    "within5pct",
                    "exact_pct",
                ]
            ].reset_index(drop=True)
            print(f"── {dtype} Results (Best Sweep Points) ──")
            _show(display_fn, out.round(4))

        flopoco_table = (
            best_baseline_df[
                (best_baseline_df["variant"] == "FloPoCo") & (best_baseline_df["dtype"] == "FP32")
            ][["op", "LUTs", "FFs", "DSPs", "Fmax_MHz", "Latency_ns", "ADP", "within5pct", "exact_pct"]]
            .rename(
                columns={
                    "op": "Operation",
                    "Fmax_MHz": "Fmax (MHz)",
                    "Latency_ns": "Latency (ns)",
                    "ADP": "ADP (LUT*ns)",
                    "within5pct": "Within-5%",
                    "exact_pct": "Exact match",
                }
            )
            .reset_index(drop=True)
        )
        if not flopoco_table.empty:
            flopoco_table = flopoco_table.round(
                {
                    "LUTs": 1,
                    "FFs": 1,
                    "DSPs": 1,
                    "Fmax (MHz)": 3,
                    "Latency (ns)": 3,
                    "ADP (LUT*ns)": 3,
                    "Within-5%": 2,
                    "Exact match": 2,
                }
            )
            print("FloPoCo baseline summary")
            _show(display_fn, flopoco_table)

            flopoco_latex_df = flopoco_table.copy()
            for col in ["Within-5%", "Exact match"]:
                if col in flopoco_latex_df.columns:
                    flopoco_latex_df[col] = flopoco_latex_df[col].map(
                        lambda x: f"{x:.2f}\\%" if pd.notna(x) else "NaN"
                    )
            for col in ["LUTs", "FFs", "DSPs"]:
                if col in flopoco_latex_df.columns:
                    flopoco_latex_df[col] = flopoco_latex_df[col].map(
                        lambda x: f"{x:.1f}" if pd.notna(x) else "NaN"
                    )
            for col in ["Fmax (MHz)", "Latency (ns)", "ADP (LUT*ns)"]:
                if col in flopoco_latex_df.columns:
                    flopoco_latex_df[col] = flopoco_latex_df[col].map(
                        lambda x: f"{x:.3f}" if pd.notna(x) else "NaN"
                    )
            flopoco_latex = flopoco_latex_df.to_latex(index=False, escape=False)
            print("LaTeX FloPoCo table:")
            print(flopoco_latex)

        plot_df = best_baseline_df.copy()
        benchmark_order = [
            "FP32 Addition",
            "FP32 Multiplication",
            "MXINT8 Addition",
            "MXINT8 Multiplication",
        ]
        plot_df["benchmark"] = plot_df["dtype"] + " " + plot_df["op"]
        plot_df["variant"] = pd.Categorical(
            plot_df["variant"], categories=["Subcomponents", "V1", "V2", "FloPoCo"], ordered=True
        )
        plot_df["benchmark"] = pd.Categorical(plot_df["benchmark"], categories=benchmark_order, ordered=True)
        plot_df = plot_df.sort_values(["benchmark", "variant"]).reset_index(drop=True)

        variant_colors_all = {
            "Subcomponents": "#2A9D8F",
            "V1": "#E76F51",
            "V2": "#457B9D",
            "FloPoCo": "#6D597A",
        }
        metrics = [
            ("LUTs", "LUTs", ".0f"),
            ("Latency_ns", "Latency (ns)", ".2f"),
            ("ADP", "ADP (LUT·ns)", ".0f"),
            ("within5pct", "Accuracy within 5% (%)", ".1f"),
        ]
        fig, axes = plt.subplots(2, 2, figsize=(14, 9), constrained_layout=True)
        axes = axes.flatten()
        x = np.arange(len(benchmark_order), dtype=float)
        width = 0.18

        for ax, (metric, ylabel, fmt) in zip(axes, metrics):
            for idx, variant in enumerate(["Subcomponents", "V1", "V2", "FloPoCo"]):
                sub = (
                    plot_df[plot_df["variant"] == variant][["benchmark", metric]]
                    .drop_duplicates(subset=["benchmark"])
                    .set_index("benchmark")
                    .reindex(benchmark_order)
                )
                vals = sub[metric].to_numpy(dtype=float) if metric in sub.columns else np.full(len(benchmark_order), np.nan)
                xpos = x + (idx - 1.5) * width
                mask = np.isfinite(vals)
                if mask.any():
                    bars = ax.bar(
                        xpos[mask],
                        vals[mask],
                        width=width,
                        label=variant,
                        color=variant_colors_all[variant],
                        edgecolor="white",
                        linewidth=0.8,
                    )
                    for bar, val in zip(bars, vals[mask]):
                        ax.annotate(
                            format(val, fmt),
                            (bar.get_x() + bar.get_width() / 2, bar.get_height()),
                            ha="center",
                            va="bottom",
                            fontsize=7,
                            xytext=(0, 2),
                            textcoords="offset points",
                        )
            ax.set_xticks(x)
            ax.set_xticklabels([b.replace(" ", "\n", 1) for b in benchmark_order], fontsize=9)
            ax.set_ylabel(ylabel)
            ax.grid(axis="y", alpha=0.25)
            ax.set_axisbelow(True)

        handles, labels = axes[0].get_legend_handles_labels()
        if handles:
            axes[0].legend(handles, labels, fontsize=8, ncol=2, loc="upper left")
        fig.suptitle("Best Baseline Results from Hyperparameter Sweep", fontsize=14)
        plt.show()

        trade_df = plot_df.dropna(subset=["ADP", "within5pct"]).copy()
        if not trade_df.empty:
            benchmark_colors = {
                "FP32 Addition": "#1D3557",
                "FP32 Multiplication": "#457B9D",
                "MXINT8 Addition": "#E76F51",
                "MXINT8 Multiplication": "#F4A261",
            }
            markers = {"Subcomponents": "o", "V1": "^", "V2": "s", "FloPoCo": "D"}
            label_offsets = {
                ("FP32 Addition", "Subcomponents"): (6, 6),
                ("FP32 Addition", "V1"): (6, -14),
                ("FP32 Addition", "V2"): (-32, 8),
                ("FP32 Addition", "FloPoCo"): (6, 6),
                ("FP32 Multiplication", "Subcomponents"): (6, 6),
                ("FP32 Multiplication", "V1"): (8, -14),
                ("FP32 Multiplication", "V2"): (-34, 8),
                ("FP32 Multiplication", "FloPoCo"): (8, 6),
                ("MXINT8 Addition", "Subcomponents"): (6, 6),
                ("MXINT8 Addition", "V1"): (6, 6),
                ("MXINT8 Addition", "V2"): (6, 6),
                ("MXINT8 Multiplication", "Subcomponents"): (6, 6),
                ("MXINT8 Multiplication", "V1"): (6, -14),
                ("MXINT8 Multiplication", "V2"): (6, 6),
            }
            short_labels = {
                "Subcomponents": "Subcomp.",
                "V1": "V1",
                "V2": "V2",
                "FloPoCo": "FloPoCo",
            }
            benchmark_short = {
                "FP32 Addition": "FP32 Add",
                "FP32 Multiplication": "FP32 Mul",
                "MXINT8 Addition": "MXINT8 Add",
                "MXINT8 Multiplication": "MXINT8 Mul",
            }

            fig, ax = plt.subplots(figsize=(10.5, 6.2), constrained_layout=True)
            for _, row in trade_df.iterrows():
                ax.scatter(
                    row["ADP"],
                    row["within5pct"],
                    color=benchmark_colors.get(str(row["benchmark"]), "gray"),
                    marker=markers.get(str(row["variant"]), "o"),
                    s=110,
                    edgecolors="black",
                    linewidth=0.7,
                )
                key = (str(row["benchmark"]), str(row["variant"]))
                dx, dy = label_offsets.get(key, (6, 6))
                label = (
                    f"{benchmark_short.get(str(row['benchmark']), str(row['benchmark']))}\n"
                    f"{short_labels.get(str(row['variant']), str(row['variant']))}"
                )
                ax.annotate(
                    label,
                    (row["ADP"], row["within5pct"]),
                    fontsize=7,
                    xytext=(dx, dy),
                    textcoords="offset points",
                    bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.85),
                )

            ax.set_xlabel("ADP (LUT·ns)")
            ax.set_ylabel("Accuracy within 5% (%)")
            ax.set_title("Best Baseline Trade-off: Accuracy vs ADP")
            ax.grid(alpha=0.25)
            ax.margins(x=0.05, y=0.08)

            benchmark_handles = [
                Line2D([0], [0], marker="o", color="w", label=lab,
                       markerfacecolor=col, markeredgecolor="black", markersize=8)
                for lab, col in benchmark_colors.items()
                if lab in trade_df["benchmark"].astype(str).unique()
            ]
            ax.legend(
                handles=benchmark_handles,
                fontsize=8,
                ncol=2,
                loc="upper center",
                bbox_to_anchor=(0.5, -0.12),
                frameon=True,
                title="Benchmark family",
            )
            plt.show()

    variant_colors = {"Subcomponents": "#1b9e77", "V1": "#d95f02", "V2": "#7570b3"}
    variant_markers = {"Subcomponents": "o", "V1": "^", "V2": "s"}

    if has_accuracy:
        fig, axes = plt.subplots(2, 2, figsize=(12.5, 8.5), constrained_layout=True, sharex=True, sharey=False)
        family_order = [
            ("FP32", "Addition"),
            ("FP32", "Multiplication"),
            ("MXINT8", "Addition"),
            ("MXINT8", "Multiplication"),
        ]

        for ax, (dtype, op) in zip(axes.ravel(), family_order):
            family = agg[(agg["dtype"] == dtype) & (agg["op"] == op)].copy()
            for variant in ["Subcomponents", "V1", "V2"]:
                vdf = family[family["variant"] == variant].copy()
                if vdf.empty:
                    continue
                best_by_timeout = (
                    vdf.sort_values(
                        ["timeout", "mean_within_rel_pct", "mean_adp", "mean_latency_ns"],
                        ascending=[True, False, True, True],
                    )
                    .groupby("timeout", as_index=False)
                    .first()
                )
                ax.plot(
                    best_by_timeout["timeout"],
                    best_by_timeout["mean_within_rel_pct"] * 100,
                    color=variant_colors[variant],
                    marker=variant_markers[variant],
                    linewidth=2.0,
                    markersize=6,
                    label=variant,
                )

                rec = vdf[vdf["is_recommended"]]
                if not rec.empty:
                    rec = rec.iloc[0]
                    ax.scatter(
                        [rec["timeout"]],
                        [rec["mean_within_rel_pct"] * 100],
                        s=90,
                        color=variant_colors[variant],
                        edgecolor="black",
                        linewidth=1.1,
                        zorder=4,
                    )

            ax.set_title(f"{dtype} {op}")
            ax.set_xlabel("Solver timeout (s)")
            ax.set_ylabel("Best mean accuracy within 5% threshold (%)")
            ax.set_ylim(0, 105)
            ax.grid(alpha=0.3)

        axes[0, 0].legend(title="Variant", fontsize=8)
        fig.suptitle(
            "Hyperparameter Sweep: Diminishing Returns with Increasing Solver Timeout",
            fontsize=14,
        )
        plt.show()

    if has_accuracy and has_adp:
        fig, ax = plt.subplots(figsize=(8.5, 5.8), constrained_layout=True)
        rec_points = agg[agg["is_recommended"]].dropna(subset=["mean_within_rel_pct", "mean_adp"]).copy()
        op_markers = {"Addition": "o", "Multiplication": "s"}

        for _, row in rec_points.iterrows():
            x = row["mean_within_rel_pct"] * 100
            y = row["mean_adp"]
            ax.scatter(
                x,
                y,
                color=variant_colors.get(row["variant"], "#444"),
                marker=op_markers.get(row["op"], "o"),
                s=110,
                edgecolor="black",
                linewidth=1.0,
                zorder=3,
            )
            ax.annotate(
                f"{row['dtype']} {row['op']}\n{row['variant']}\n({row['timeout']}s, {row['num_iterations']})",
                (x, y),
                xytext=(8, 6 if row["op"] == "Addition" else -14),
                textcoords="offset points",
                fontsize=8,
                bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="0.7", alpha=0.9),
            )

        ax.set_xlabel("Mean accuracy within 5% threshold (%)")
        ax.set_ylabel("Mean ADP (LUT*ns)")
        ax.set_yscale("log")
        ax.grid(alpha=0.3)

        variant_handles = [
            Line2D([0], [0], marker="o", color="w", label=variant, markerfacecolor=color, markersize=8)
            for variant, color in variant_colors.items()
        ]
        op_handles = [
            Line2D([0], [0], marker=marker, color="#444", label=op, linestyle="None", markersize=8)
            for op, marker in op_markers.items()
        ]
        ax.legend(handles=variant_handles + op_handles, fontsize=8, loc="lower right")
        fig.suptitle(
            "Hyperparameter Sweep: Recommended Points Only",
            fontsize=14,
        )
        plt.show()

    return {
        "hp_dir": hp_dir,
        "hp_files": hp_files,
        "hp_df": hp_df,
        "hp_agg": agg.copy(),
        "hp_recommended": hp_recommended,
        "hp_completeness_df": hp_completeness_df,
        "hp_missing_df": hp_missing_df,
        "hp_recommended_table": recommended_table,
        "hp_recommended_latex": recommended_latex.to_latex(index=False, escape=False),
        "hp_best_baseline_df": best_baseline_df if 'best_baseline_df' in locals() else pd.DataFrame(),
        "hp_flopoco_table": flopoco_table,
        "hp_flopoco_latex": flopoco_latex,
    }
