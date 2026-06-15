#!/usr/bin/env bash
set -euo pipefail

moon test --target wasm-gc
moon test --target js
moon test --target native
moon test --target wasm
