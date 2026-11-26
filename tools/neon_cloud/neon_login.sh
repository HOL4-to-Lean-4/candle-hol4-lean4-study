#!/bin/bash
# Start the interactive agy sign-in in tmux session "agy" and print the Google auth URL.
# Then paste the user's code with:  bash neon_login.sh --code '<code>'
# The prompt lives only in this running process: the machine must stay awake until
# the code arrives (keep a background job running), or the code will not match.
eval "$(bash "$(dirname "$0")/start_keyring.sh")"
export PATH=$HOME/.local/bin:$PATH
if [ "${1:-}" = "--code" ]; then
  tmux send-keys -t agy -l "$2"; sleep 1; tmux send-keys -t agy Enter; sleep 15
  for i in 1 2 3 4 5; do tmux send-keys -t agy Enter; sleep 2; done   # onboarding screens
  tmux kill-session -t agy 2>/dev/null
  exec bash "$(dirname "$0")/neon_check.sh"
fi
tmux kill-session -t agy 2>/dev/null
tmux new-session -d -s agy -x 250 -y 50 "export DBUS_SESSION_BUS_ADDRESS=$DBUS_SESSION_BUS_ADDRESS; export PATH=$PATH; cd ~; agy"
sleep 10; tmux send-keys -t agy Enter; sleep 8     # choose "1. Google OAuth"
tmux capture-pane -p -t agy -J -S -100 | sed 's/^ *//;s/ *$//' \
  | awk '/^https:\/\/accounts/{f=1} f&&/^If you/{f=0} f' | tr -d '\n'; echo
