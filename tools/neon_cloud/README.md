# Gemini Neon reviewer in a Claude cloud session

One long-lived cloud thread ("Set up Gemini Neon in a cloud session") stays signed in to
the Antigravity CLI `agy` on the user's Google subscription and runs every Neon review
for the migration. Other threads hand requests to it. Only the official `agy` binary is
invoked; OAuth tokens stay in the keyring and are never read or copied out.

## Facts found (2026-11-26)

- agy 1.5.17. Model ids: `gemini-4-neon-{low,medium,high,xhigh}` (`agy models`).
  Default here: `gemini-4-neon-high`. Test reply: "I am Gemini 4 Neon".
- The cloud network blocks `antigravity.google`, so the official install script cannot
  run. `install_agy.sh` downloads the official Linux build from
  `storage.googleapis.com/antigravity-public` and checks the bucket's MD5.
- Sign-in uses Google OAuth with PKCE: agy prints a URL, the user signs in and pastes
  back a code. The code only matches the agy process that printed the URL.
- The cloud machine restarts when the session is idle (about 20 min). Files in `$HOME`
  and apt packages survive; running processes (agy prompt, D-Bus, keyring) do not.
  Keep a background job running while waiting for a code.
- agy stores the token in the Secret Service keyring (log: "authenticated via keyring").
  `start_keyring.sh` starts D-Bus at `/run/agy-dbus.sock` and an unlocked gnome-keyring
  (empty keyring password; D-Bus activation would otherwise start it locked). The
  keyring file `~/.local/share/keyrings/login.keyring` survives restarts, so the login
  does too.
- Print mode: `agy --model M --output-format json -p "..."` (`-p` must be last, or it
  swallows the next flag). Output has `response`, `conversation_id`, `usage`.
  Neon can read files in its working directory; tools needing approval are denied.
  Do not use `--mode plan`: it writes plan artifacts and asks for approval.

## Scripts

| script | use |
|---|---|
| `install_agy.sh` | install agy + keyring packages (idempotent) |
| `start_keyring.sh` | start D-Bus + unlocked keyring; prints the `export` line |
| `neon_check.sh` | exit 0 signed in, 2 needs sign-in, 1 other error |
| `neon_login.sh` | print sign-in URL; `--code CODE` completes it |
| `neon_review.sh DIR` | run `DIR/prompt.md` through Neon; writes `response.md`, `response.json` |

## Hand-off protocol for other threads

1. Make a request folder `/mnt/project-files/neon_reviews/<YYYYMMDD-HHMM>-<slug>/`
   holding `prompt.md` (the full review instructions, self-contained) and the files to
   review. Never put HOL4 proofs in a prover-facing request.
2. Message the Neon thread with the folder path (and the requesting thread id).
3. The Neon thread runs `neon_review.sh <folder>`, copies `response.md` and
   `response.json` into the folder, appends a row to `neon_reviews/ledger.tsv`
   (time, folder, model, conversation id, tokens, status), and messages the requester.
4. Several requests may run in parallel; each folder is independent.

## Login drop and recovery

- Before every review `neon_review.sh` runs `neon_check.sh`. Exit 2 means the login is
  gone (keyring file lost, token revoked, or refresh failed).
- Then the Neon thread runs `neon_login.sh`, starts a background keep-alive job, posts
  the URL to the user, and on the code runs `neon_login.sh --code CODE`. Queued
  requests wait and are run after sign-in; requesters are told about the delay.
- A container rebuild (new session, not a restart) loses `$HOME`: rerun
  `install_agy.sh` and sign in again.
