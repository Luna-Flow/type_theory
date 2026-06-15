#!/usr/bin/env bash
set -euo pipefail

moon fmt
moon check --target all
moon info
./run_test.sh
