set shell := ["bash", "-cu"]

default:
  @just --list

check:
  moon check --target all

test:
  ./run_test.sh

ready:
  ./ready_to_pr.sh
