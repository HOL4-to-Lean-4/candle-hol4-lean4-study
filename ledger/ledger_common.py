"""Shared helpers for the cost-ledger extractors (stdlib only)."""
import argparse
import csv
import socket
from pathlib import Path

COLUMNS = [
    "arm", "phase", "round", "workflow", "run", "tool", "model_id",
    "start_utc", "end_utc", "input_tokens", "output_tokens",
    "cache_read_tokens", "cache_write_tokens", "reasoning_tokens",
    "usd_billed", "usd_api_equivalent", "aristotle_tasks", "aristotle_minutes",
    "human_minutes", "machine", "notes",
]
DEFAULT_LEDGER = Path(__file__).resolve().parent / "costs.csv"


def base_parser(description):
    p = argparse.ArgumentParser(description=description)
    p.add_argument("files", nargs="+", type=Path, help="session transcript files")
    p.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    for col in ("arm", "phase", "round", "workflow", "run", "usd_billed",
                "usd_api_equivalent", "aristotle_tasks", "aristotle_minutes",
                "human_minutes", "notes"):
        p.add_argument("--" + col.replace("_", "-"), dest=col, default="")
    p.add_argument("--machine", default=socket.gethostname())
    p.add_argument("--dry-run", action="store_true", help="print rows, do not append")
    return p


def existing_keys(ledger):
    """Session keys already in the ledger (notes field starts with 'session=<id>')."""
    if not ledger.exists():
        return set()
    with ledger.open(newline="", encoding="utf-8") as f:
        return {r["notes"].split(";")[0] for r in csv.DictReader(f) if r.get("notes")}


def append_rows(ledger, rows, dry_run=False):
    new = not ledger.exists()
    seen = existing_keys(ledger)
    out = []
    for r in rows:
        key = r["notes"].split(";")[0]
        if key in seen:
            print(f"skip (already in ledger): {key}")
            continue
        seen.add(key)
        out.append(r)
    if dry_run:
        w = csv.DictWriter(__import__("sys").stdout, fieldnames=COLUMNS)
        w.writeheader()
        w.writerows(out)
        return out
    ledger.parent.mkdir(parents=True, exist_ok=True)
    with ledger.open("a", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=COLUMNS)
        if new:
            w.writeheader()
        w.writerows(out)
    print(f"appended {len(out)} row(s) to {ledger}")
    return out


def row_from_args(args, **fields):
    row = {c: "" for c in COLUMNS}
    for c in COLUMNS:
        v = getattr(args, c, "")
        if v:
            row[c] = v
    row.update({k: v for k, v in fields.items() if v is not None})
    if args.notes:
        row["notes"] = fields["notes"] + ";" + args.notes
    return row
