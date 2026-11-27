# Astra through the SSS gateway

The SSS gateway (`api.ssstoken.net`) is an OpenAI-compatible API (Responses and Chat Completions). Cloud sessions reach it when the project uses the cloud environment "Default", which sets `SSS_BASE_URL` and `SSS_GPT_KEY` and allows the host. The scripts read the key from the environment and never write it to a file or log.

| Script | Use |
|---|---|
| `astra.py models` | List the models the gateway offers. |
| `astra.py probe [-m MODEL]` | One tiny call. Prints the model the gateway reports and the token usage. |
| `astra.py ask [-m MODEL] [-e high] -o OUT < prompt.md` | One call without tools. Writes `OUT.txt` and `OUT.meta.json`. |
| `codex_astra.sh WORKDIR OUT [MODEL] < prompt.md` | `codex exec` with the same flags as `audit/real/run.py` step S1, with the gateway as Codex's model provider. Astra can read the files in `WORKDIR` (read-only sandbox). Writes `OUT.raw`, `OUT.last`, `OUT.err`, `OUT.meta.json`. |

Install Codex once per session: `npm install -g @openai/codex` (0.172.0 on 27 Nov 2026). The wrapper uses `CODEX_HOME=~/.codex-sss`, so it does not touch another Codex login.

## Logging the reported model

Codex JSON events carry token usage but no model name. `codex_astra.sh` therefore makes one probe call to the same model just before the run and stores the model the gateway reports in `OUT.meta.json` (`reported_model`, plus the probe's own usage). `astra.py ask` stores the `model` field of the response itself.

## Smoke test, 27 November 2026

| Model requested | Model reported | Input tokens (cached) for "Reply with exactly: OK" | Output |
|---|---|---|---|
| `gpt-6.2-astra` | `gpt-6.2-astra` | 16,198 (14,080) | 10 |
| `gpt-6-astra` | `gpt-6-astra` | 14,766 (12,544) | 48 (36 reasoning) |

Both names resolve, through `/v1/responses` and `/v1/chat/completions`. The gateway adds about 14,000 to 16,000 input tokens to every call (a fixed prompt that the client does not send; most of it is cached), and the amount differs between the two models. A `codex exec` run that reads one small file used 34,000 to 36,000 input tokens (22,000 cached). The gateway reports what it serves; the scripts cannot check that independently.

Models listed by `/v1/models`: codex-auto-review, gpt-5.3-codex-spark, gpt-5.6, gpt-5.6-sol, gpt-5.6-terra, gpt-6, gpt-6-astra, gpt-6-sol, gpt-6.1-sol, gpt-6.1-terra, gpt-6.2-astra, gpt-6.2-sol, and gpt-image-2 / 2.5 / 2.6 variants.
