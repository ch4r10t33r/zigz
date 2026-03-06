#!/usr/bin/env sh
# Install Zig (default 0.15.2). One-liner: curl -sL https://raw.githubusercontent.com/ch4r10t33r/zigz/main/scripts/install_zig.sh | sh
# Optional: pass version, e.g. sh install_zig.sh 0.15.2. To get PATH for eval: script prints export line to stdout at end.
set -e
VERSION="${1:-0.15.2}"
PREFIX="${ZIG_INSTALL_DIR:-$HOME/.local}"
BASE="https://ziglang.org/download/${VERSION}"
case "$(uname -s)" in
  Linux)  OS=linux ;;
  Darwin) OS=macos ;;
  *) echo "Unsupported OS" >&2; exit 1 ;;
esac
case "$(uname -m)" in
  x86_64|amd64) ARCH=x86_64 ;;
  aarch64|arm64) ARCH=aarch64 ;;
  *) echo "Unsupported arch" >&2; exit 1 ;;
esac
FILE="zig-${ARCH}-${OS}-${VERSION}.tar.xz"
URL="${BASE}/${FILE}"
echo "Installing Zig ${VERSION} to ${PREFIX}..." >&2
mkdir -p "${PREFIX}"
curl -sL "${URL}" | tar -xJ -C "${PREFIX}"
DIR="${PREFIX}/zig-${ARCH}-${OS}-${VERSION}"
echo "export PATH=\"${DIR}:\$PATH\""
