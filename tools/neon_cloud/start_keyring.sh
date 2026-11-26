#!/bin/bash
# Start a session D-Bus at a fixed socket and make sure gnome-keyring's "login"
# collection (Secret Service) is running and UNLOCKED. Safe to run repeatedly.
SOCK=/run/agy-dbus.sock
export DBUS_SESSION_BUS_ADDRESS=unix:path=$SOCK
if ! dbus-send --session --dest=org.freedesktop.DBus --print-reply / org.freedesktop.DBus.ListNames >/dev/null 2>&1; then
  rm -f $SOCK
  dbus-daemon --session --address=$DBUS_SESSION_BUS_ADDRESS --fork --nopidfile
fi
locked=$(dbus-send --session --dest=org.freedesktop.secrets --print-reply \
  /org/freedesktop/secrets/collection/login org.freedesktop.DBus.Properties.Get \
  string:org.freedesktop.Secret.Collection string:Locked 2>/dev/null | awk '/boolean/{print $3}')
if [ "$locked" != "false" ]; then
  # D-Bus activation may have started the daemon locked; replace it with an unlocked one.
  # The keyring password is empty: the container itself is the security boundary.
  echo "" | gnome-keyring-daemon --replace --unlock --components=secrets --daemonize >/dev/null 2>&1
  sleep 1
fi
echo "export DBUS_SESSION_BUS_ADDRESS=$DBUS_SESSION_BUS_ADDRESS"
