#!/usr/bin/env bash
# P3: an unvalidated request header does not reach the webhook processor.
# Real Nexus file, Crux.Api.Endpoints.CommunicationsWebhookEndpoints.SendGridMarketingWebhook.
# The copy in real/ has its em dashes replaced by '-' (the frontend's byte/char span bug).
set -eu
ROOT=$(CDPATH= cd -- "$(dirname "$0")/../../../.." && pwd)
PROVER=${PROVER:-$ROOT/scry/build/prover}
exec "$PROVER" "$ROOT/scry/corpus/prover/real/CommunicationsWebhookEndpoints.cs" \
  Crux.Api.Endpoints.CommunicationsWebhookEndpoints.SendGridMarketingWebhook \
  --pack "$ROOT/scry/corpus/prover/packs/webhook.scry"
