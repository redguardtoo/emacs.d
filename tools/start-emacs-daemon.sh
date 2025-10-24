#!/bin/sh

# Usage:
# Start daemon: ./start-emacs-daemon.sh
# Stop daemon: ./start-emacs-daemon.sh stop

OS=`uname -s`

# set up SSH_AUTH_SOCK, macOS only
if [ "$OS" = "Darwin" ]; then
  export SSH_AUTH_SOCK=`launchctl getenv SSH_AUTH_SOCK`
fi

# clean up old server related files
rm -f "$HOME/.emacs.d/server/server"

# set up emacs executable path
if [ "$OS" = "Darwin" ]; then
  EMACS="/opt/homebrew/bin/emacs"
else
  EMACS="/usr/bin/emacs"
fi

# Start or stop Emacs daemon
if [ "$1" = "stop" ]; then
  emacsclient --eval "(kill-emacs)"
else
  EXTRA_ARGS=""

  if [ -f "$HOME/.gnus.el" ]; then
    EXTRA_ARGS="$EXTRA_ARGS -l $HOME/.gnus.el"
  fi

  if [ -f "$HOME/.emacs-daemon-setup.el" ]; then
    EXTRA_ARGS="$EXTRA_ARGS -l $HOME/.emacs-daemon-setup.el"
  fi
  exec "$EMACS" -Q --daemon \
    -l "$HOME/.emacs.d/early-init.el" \
    -l "$HOME/.emacs.d/init.el" \
    $EXTRA_ARGS \
    --eval "(progn (require 'server) (unless (server-running-p) (server-start)) (require 'org) (require 'emms))"

  # macOS notification
  if [ "$OS" = "Darwin" ]; then
    osascript -e 'display notification "Emacs daemon started successfully" with title "Emacs Service"'
  fi
fi