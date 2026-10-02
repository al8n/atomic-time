#!/bin/bash
set -e

if [ "$#" -eq 0 ]; then
  echo "Error: rustup toolchain install requires arguments" >&2
  exit 1
fi

for retry_delay in 30 60 120; do
  if rustup toolchain install "$@"; then
    exit 0
  fi

  echo "rustup toolchain install failed; retrying in ${retry_delay}s" >&2
  sleep "$retry_delay"
done

rustup toolchain install "$@"
