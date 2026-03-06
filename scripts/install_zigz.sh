#!/usr/bin/env sh
# Install zigz (zkVM CLI). One-liner: curl -sL https://raw.githubusercontent.com/ch4r10t33r/zigz/main/scripts/install_zigz.sh | sh
# Optional: pass version/tag, e.g. sh install_zigz.sh v0.1.0 (default: latest release).
set -e
TAG="${1:-latest}"
PREFIX="${ZIGZ_INSTALL_DIR:-$HOME/.local}"
BIN_DIR="${PREFIX}/bin"
REPO="ch4r10t33r/zigz"
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
ZIGZ_NAME="zigz-${OS}-${ARCH}"

install_from_release() {
  if [ "$TAG" = "latest" ]; then
    API="https://api.github.com/repos/${REPO}/releases/latest"
  else
    API="https://api.github.com/repos/${REPO}/releases/tags/${TAG}"
  fi
  URL=$(curl -sL "$API" | grep "browser_download_url" | grep "$ZIGZ_NAME" | head -1 | sed 's/.*"\(https[^"]*\)".*/\1/')
  if [ -n "$URL" ]; then
    echo "Downloading zigz from release..." >&2
    mkdir -p "$BIN_DIR"
    curl -sL "$URL" -o "${BIN_DIR}/zigz"
    chmod +x "${BIN_DIR}/zigz"
    echo "Installed zigz to ${BIN_DIR}/zigz" >&2
    echo "export PATH=\"${BIN_DIR}:\$PATH\""
    return 0
  fi
  return 1
}

build_from_source() {
  echo "No pre-built binary for ${OS}-${ARCH}; building from source..." >&2
  BUILD_DIR="${TMPDIR:-/tmp}/zigz-build-$$"
  trap "rm -rf ${BUILD_DIR}" EXIT
  git clone --depth 1 https://github.com/${REPO}.git "${BUILD_DIR}"
  cd "${BUILD_DIR}"
  if [ -x "./scripts/install_zig.sh" ]; then
    eval $(./scripts/install_zig.sh 0.15.2)
  fi
  zig build -Doptimize=ReleaseSafe
  mkdir -p "$BIN_DIR"
  cp zig-out/bin/zigz "${BIN_DIR}/zigz"
  chmod +x "${BIN_DIR}/zigz"
  echo "Built and installed zigz to ${BIN_DIR}/zigz" >&2
  echo "export PATH=\"${BIN_DIR}:\$PATH\""
}

if ! install_from_release; then
  build_from_source
fi
