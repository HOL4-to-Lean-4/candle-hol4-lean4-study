"""Append one ledger row per Codex rollout.

Input: ~/.codex/sessions/YYYY/MM/DD/rollout-<timestamp>-<thread_id>.jsonl.
Usage is the last token_count event's info.total_token_usage. The model and
reasoning effort come from turn_context events.

Example:
  python ledger/extract_codex.py ~/.codex/sessions/2026/11/14/rollout-*.jsonl \
      --arm setup --phase setup
"""
import json
from pathlib import Path

from ledger_common import append_rows, base_parser, row_from_args


def main():
    p = base_parser(__doc__)
    p.add_argument("--tool", default="codex-cli")
    args = p.parse_args()
    rows = []
    for path in args.files:
        total, models, efforts, times, sid = None, [], [], [], None
        with Path(path).open(encoding="utf-8") as f:
            for line in f:
                try:
                    o = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if o.get("timestamp"):
                    times.append(o["timestamp"])
                pl = o.get("payload") or {}
                if o.get("type") == "session_meta":
                    sid = pl.get("id") or pl.get("session_id")
                elif o.get("type") == "turn_context":
                    if pl.get("model") and pl["model"] not in models:
                        models.append(pl["model"])
                    eff = pl.get("effort") or pl.get("reasoning_effort")
                    if eff and eff not in efforts:
                        efforts.append(eff)
                elif o.get("type") == "event_msg" and pl.get("type") == "token_count":
                    info = pl.get("info") or {}
                    if info.get("total_token_usage"):
                        total = info["total_token_usage"]
        total = total or {}
        times.sort()
        inp = total.get("input_tokens", 0)
        cached = total.get("cached_input_tokens", 0)
        row = row_from_args(
            args,
            tool=args.tool,
            model_id="+".join(models),
            start_utc=times[0] if times else "",
            end_utc=times[-1] if times else "",
            # Codex input_tokens includes cached tokens; report the uncached part here.
            input_tokens=inp - cached,
            output_tokens=total.get("output_tokens", 0),
            cache_read_tokens=cached,
            cache_write_tokens=total.get("cache_write_input_tokens", 0),
            reasoning_tokens=total.get("reasoning_output_tokens", 0),
            notes=f"session={sid or Path(path).stem}",
        )
        row["notes"] += f";effort={'+'.join(efforts)}"
        rows.append(row)
    append_rows(args.ledger, rows, args.dry_run)


if __name__ == "__main__":
    main()
