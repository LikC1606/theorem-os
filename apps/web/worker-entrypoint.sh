#!/bin/sh
set -eu
case "${1:-standard}" in
  mathlib)
    # FUSE mounts need a capability scoped to this new user namespace only.
    exec bwrap --unshare-user --uid 0 --gid 0 --cap-add CAP_SYS_ADMIN --cap-add CAP_SETFCAP \
      --bind / / --dev-bind /dev /dev --proc /proc --die-with-parent \
      -- bun apps/web/worker.ts
    ;;
  standard) exec bun apps/web/worker.ts ;;
  *) exit 2 ;;
esac
