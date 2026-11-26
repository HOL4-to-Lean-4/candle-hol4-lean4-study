#!/bin/bash
# Install the Antigravity CLI (agy) and a Secret Service keyring in a Claude cloud container.
# antigravity.google is blocked by the cloud network, so the official install script
# cannot run. This fetches the same official Linux build from Google's public bucket
# (the bucket the Windows package also uses) and checks it against the bucket's MD5.
set -euo pipefail
VER=${AGY_VERSION:-1.5.17-4823843970351104}
URL=https://storage.googleapis.com/antigravity-public/antigravity-cli/$VER/linux-x64/cli_linux_x64.tar.gz
if ! command -v gnome-keyring-daemon >/dev/null || ! command -v tmux >/dev/null; then
  apt-get install -y -q gnome-keyring libsecret-tools dbus-x11 tmux >/dev/null 2>&1 || \
    { apt-get update -q >/dev/null && apt-get install -y -q gnome-keyring libsecret-tools dbus-x11 tmux >/dev/null; }
fi
if [ ! -x "$HOME/.local/bin/agy" ]; then
  d=$(mktemp -d); cd "$d"
  curl -fsS -m 600 -o cli.tgz "$URL"
  want=$(curl -sI -m 30 "$URL" | tr -d '\r' | awk -F'md5=' 'tolower($0)~/x-goog-hash: md5=/{print $2}')
  got=$(python3 -c "import hashlib,base64,sys;print(base64.b64encode(hashlib.md5(open('cli.tgz','rb').read()).digest()).decode())")
  [ "$want" = "$got" ] || { echo "MD5 mismatch: $want vs $got" >&2; exit 1; }
  tar xzf cli.tgz
  mkdir -p "$HOME/.local/bin"; install -m 755 antigravity "$HOME/.local/bin/agy"
fi
"$HOME/.local/bin/agy" --version
