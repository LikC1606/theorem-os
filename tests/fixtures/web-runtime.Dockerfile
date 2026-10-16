ARG BASE_IMAGE=theorem-os-worker:local
FROM ${BASE_IMAGE}
USER root
RUN rm -f /usr/local/bin/codex
COPY --chmod=0555 tests/fixtures/web-codex.mjs /usr/local/bin/codex
LABEL org.theoremos.fixture="web-runtime-no-provider"
USER 10001:10001
