FROM oven/bun:1.4.0 AS bun
FROM docker:29-cli AS docker-cli

FROM node:22-bookworm-slim AS base
COPY --from=bun /usr/local/bin/bun /usr/local/bin/bun
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git python3 util-linux bubblewrap elan \
    && rm -rf /var/lib/apt/lists/*
WORKDIR /opt/theorem-os
COPY package.json bun.lock tsconfig.json extraction.json ./
RUN bun install --frozen-lockfile

FROM base AS source
COPY bin ./bin
COPY src ./src
COPY scripts ./scripts
COPY resources ./resources
COPY apps ./apps
COPY docs/assets ./docs/assets
COPY LICENSE ./LICENSE

FROM base AS worker-tools
ENV ELAN_HOME=/opt/elan \
    PATH=/opt/elan/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin \
    HOME=/work/home \
    DEEPSCIENTIST_MATH_SANDBOX_BACKEND=bwrap \
    DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS=/opt/elan
RUN npm install --global @openai/codex@0.162.0 \
    && elan toolchain install leanprover/lean4:v4.33.0 \
    && chmod -R a+rX /opt/elan \
    && mkdir -p /work && chown 10001:10001 /work

FROM worker-tools AS worker-mathlib
RUN apt-get -o Acquire::Retries=3 update && apt-get install -y --no-install-recommends \
    build-essential fuse3 squashfuse squashfs-tools \
    && rm -rf /var/lib/apt/lists/*
COPY resources/mathlib/environment.json ./resources/mathlib/environment.json
COPY scripts/prepare-web-mathlib.ts ./scripts/prepare-web-mathlib.ts
RUN --mount=type=cache,id=theoremos-mathlib-v4.33.0,target=/var/cache/theoremos-mathlib,sharing=locked \
    MATHLIB_CACHE_DIR=/var/cache/theoremos-mathlib bun scripts/prepare-web-mathlib.ts \
    && chmod -R a+rX /opt/theoremos-mathlib \
    && chown 10001:10001 /var/tmp && chmod 0700 /var/tmp

FROM worker-mathlib AS worker
ENV TMPDIR=/tmp \
    PATH=/opt/elan/toolchains/leanprover--lean4---v4.33.0/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin \
    DEEPSCIENTIST_MATH_TRUSTED_ELAN_ROOTS=/opt/elan/toolchains/leanprover--lean4---v4.33.0 \
    DEEPSCIENTIST_MATH_TRUSTED_CACHE_ROOTS=/opt/theoremos-mathlib/.lake/packages
COPY --from=source /opt/theorem-os /opt/theorem-os
# Use the installed binaries directly: the verifier mounts the toolchain read-only.
RUN bun scripts/build.ts --state-root /opt/runtime-state > /opt/theoremos-build.json \
    && chmod -R a+rX /opt/runtime-state \
    && chmod 0555 apps/web/worker-entrypoint.sh
USER 10001:10001
ENTRYPOINT ["/opt/theorem-os/apps/web/worker-entrypoint.sh"]

FROM source AS web
COPY --from=docker-cli /usr/local/bin/docker /usr/local/bin/docker
RUN bun scripts/build-web.ts
ENV THEOREMOS_WEB_HOST=0.0.0.0 THEOREMOS_WEB_PORT=8787
EXPOSE 8787
CMD ["bun", "apps/web/server.ts"]
