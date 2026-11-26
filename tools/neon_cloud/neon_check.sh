#!/bin/bash
# Exit 0 if agy is signed in, 2 if it needs a new sign-in, 1 on other errors.
eval "$(bash "$(dirname "$0")/start_keyring.sh")"
export PATH=$HOME/.local/bin:$PATH
out=$(agy models 2>&1)
if echo "$out" | grep -q 'gemini-4-neon'; then echo SIGNED_IN; exit 0; fi
if echo "$out" | grep -qi 'sign in'; then echo NEEDS_LOGIN; exit 2; fi
echo "ERROR: $out" | head -5; exit 1
