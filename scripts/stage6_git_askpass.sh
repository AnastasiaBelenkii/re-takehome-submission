#!/bin/sh
case "$1" in
  *Username*) printf '%s\n' 'x-access-token' ;;
  *) exec sed -n '1p' /root/.stage6-github-token ;;
esac
