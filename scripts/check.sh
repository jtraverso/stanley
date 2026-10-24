#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build --wfail
lake build Audit --wfail
lake build Challenge
lake comparator --config comparator.json
