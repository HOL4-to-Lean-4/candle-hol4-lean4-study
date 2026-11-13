"""Append one ledger row per Claude Code session transcript.

Input: ~/.claude/projects/<project>/<session-id>.jsonl. Usage is summed over
assistant messages, counting each API message id once (streamed chunks repeat it).
With --include-subagents, transcripts in <session-id>/subagents/*.jsonl are added
to the parent session's totals.

Example:
  python ledger/extract_claude.py ~/.claude/projects/X/<id>.jsonl \
      --arm setup --phase setup --tool claude-code --include-subagents
"""
import json
from collections import Counter
from pathlib import Path

from ledger_common import append_rows, base_parser, row_from_args


def read_usage(path, seen, times):
    with Path(path).open(encoding="utf-8") as f:
        for line in f:
            try:
                o = json.loads(line)
            except json.JSONDecodeError:
                continue
            ts = o.get("timestamp")
            if ts:
                times.append(ts)
            msg = o.get("message")
            if o.get("type") != "assistant" or not isinstance(msg, dict):
                continue
            u = msg.get("usage")
            if not u:
                continue
            key = msg.get("id") or o.get("requestId") or o.get("uuid")
            # keep the last chunk for each message id (it carries the final output count)
            seen[key] = (u, msg.get("model"))


def main():
    p = base_parser(__doc__)
    p.add_argument("--tool", default="claude-code")
    p.add_argument("--include-subagents", action="store_true")
    args = p.parse_args()
    rows = []
    for path in args.files:
        seen, times = {}, []
        files = [path]
        sub = path.with_suffix("") / "subagents"
        if args.include_subagents and sub.is_dir():
            files += sorted(sub.glob("*.jsonl"))
        for fp in files:
            read_usage(fp, seen, times)
        tot = Counter()
        models = Counter()
        for u, m in seen.values():
            if m and m != "<synthetic>":
                models[m] += 1
            tot["in"] += u.get("input_tokens", 0) or 0
            tot["out"] += u.get("output_tokens", 0) or 0
            tot["cr"] += u.get("cache_read_input_tokens", 0) or 0
            tot["cw"] += u.get("cache_creation_input_tokens", 0) or 0
        times.sort()
        rows.append(row_from_args(
            args,
            tool=args.tool,
            model_id="+".join(m for m, _ in models.most_common()),
            start_utc=times[0] if times else "",
            end_utc=times[-1] if times else "",
            input_tokens=tot["in"], output_tokens=tot["out"],
            cache_read_tokens=tot["cr"], cache_write_tokens=tot["cw"],
            reasoning_tokens="",
            notes=f"session={path.stem}",
        ))
        rows[-1]["notes"] += f";files={len(files)};api_messages={len(seen)}"
    append_rows(args.ledger, rows, args.dry_run)


if __name__ == "__main__":
    main()
