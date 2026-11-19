#!/usr/bin/env bash
# Source this file from Bash.
AF_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export PATH="$AF_ROOT/.venv/bin:$HOME/.elan/bin:$HOME/.local/bin:$PATH"
# Mathlib's downloaded curl expects Debian's CA path; use AlmaLinux's bundle.
if [[ -f /etc/pki/tls/certs/ca-bundle.crt ]]; then
  export CURL_CA_BUNDLE=/etc/pki/tls/certs/ca-bundle.crt
  export SSL_CERT_FILE=/etc/pki/tls/certs/ca-bundle.crt
fi
