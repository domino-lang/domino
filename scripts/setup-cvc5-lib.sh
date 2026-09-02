#!/usr/bin/env bash
#
# Sets up the build prerequisites for the `cvc5-lib` cargo feature (the native cvc5 backend used
# by `domino debug`). It is NOT needed for a default build of domino.
#
# Supports Linux (x86_64/arm64) and macOS (x86_64/arm64).
#
# It downloads, into ~/.cache/domino unless $DOMINO_CVC5_CACHE is set:
#   * a prebuilt static cvc5 release (libcvc5.a + libcvc5parser.a + C API headers), and
#   * on Linux, a libclang shared library (only if one is not already visible to bindgen);
#     on macOS, it locates the libclang.dylib that ships with Xcode / the Command Line Tools.
#
# It then writes an env file and prints the `source` line you need:
#
#   scripts/setup-cvc5-lib.sh
#   source ~/.cache/domino/cvc5-lib-env.sh
#   cargo test --workspace --features cvc5-lib
#
# Re-running is cheap: existing downloads are reused.

set -euo pipefail

CVC5_VERSION="${CVC5_VERSION:-1.3.1}"
LIBCLANG_WHEEL_VERSION="${LIBCLANG_WHEEL_VERSION:-18.1.1}"
CACHE="${DOMINO_CVC5_CACHE:-$HOME/.cache/domino}"
ENV_FILE="$CACHE/cvc5-lib-env.sh"

mkdir -p "$CACHE"

# ---------------------------------------------------------------------------
# 0. Platform detection
# ---------------------------------------------------------------------------
UNAME_S="$(uname -s)"
UNAME_M="$(uname -m)"

case "$UNAME_S" in
  Linux) CVC5_OS="Linux" ;;
  Darwin) CVC5_OS="macOS" ;;
  *)
    echo "error: unsupported OS '$UNAME_S' (only Linux and macOS have prebuilt cvc5 releases)" >&2
    exit 1
    ;;
esac

case "$UNAME_M" in
  x86_64) CVC5_ARCH="x86_64" ;;
  arm64|aarch64) CVC5_ARCH="arm64" ;;
  *)
    echo "error: unsupported architecture '$UNAME_M'" >&2
    exit 1
    ;;
esac

# ---------------------------------------------------------------------------
# 1. Prebuilt static cvc5
# ---------------------------------------------------------------------------
CVC5_DIR="$CACHE/cvc5-$CVC5_VERSION-$CVC5_OS-$CVC5_ARCH-static"
if [[ ! -f "$CVC5_DIR/lib/libcvc5.a" || ! -f "$CVC5_DIR/lib/libcvc5parser.a" ]]; then
  echo "downloading cvc5 $CVC5_VERSION (non-GPL static build for $CVC5_OS-$CVC5_ARCH) ..." >&2
  url="https://github.com/cvc5/cvc5/releases/download/cvc5-$CVC5_VERSION/cvc5-$CVC5_OS-$CVC5_ARCH-static.zip"
  tmp="$(mktemp -d)"
  curl -fsSL -o "$tmp/cvc5.zip" "$url"
  python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).extractall(sys.argv[2])" "$tmp/cvc5.zip" "$tmp"
  rm -rf "$CVC5_DIR"
  mv "$tmp/cvc5-$CVC5_OS-$CVC5_ARCH-static" "$CVC5_DIR"
  rm -rf "$tmp"
fi
echo "cvc5:      $CVC5_DIR" >&2

# ---------------------------------------------------------------------------
# 2. libclang for bindgen (only if the system has none)
# ---------------------------------------------------------------------------
LIBCLANG_LINE=""

if [[ "$CVC5_OS" == "macOS" ]]; then
  # macOS ships libclang.dylib with Xcode / the Command Line Tools; there is no prebuilt
  # libclang wheel for macOS, so we only ever look for the system one. Unlike Linux's ldconfig
  # paths, this is never on bindgen's default search path, so LIBCLANG_PATH must always be
  # written into the env file — even if it's already set in *this* shell (the file has to be
  # self-contained for whatever shell it gets sourced in later).
  resolved_libclang_dir="${LIBCLANG_PATH:-}"
  if [[ -z "$resolved_libclang_dir" ]]; then
    clang_bin="$(xcrun --find clang 2>/dev/null || true)"
    if [[ -n "$clang_bin" ]]; then
      candidate_dir="$(cd "$(dirname "$clang_bin")/../lib" 2>/dev/null && pwd || true)"
      if [[ -n "$candidate_dir" && -f "$candidate_dir/libclang.dylib" ]]; then
        resolved_libclang_dir="$candidate_dir"
      fi
    fi
  fi

  if [[ -z "$resolved_libclang_dir" ]]; then
    echo "error: could not find libclang.dylib." >&2
    echo "       install the Xcode Command Line Tools (xcode-select --install) and re-run," >&2
    echo "       or set \$LIBCLANG_PATH yourself to a directory containing libclang.dylib." >&2
    exit 1
  fi
  echo "libclang:  $resolved_libclang_dir" >&2
  LIBCLANG_LINE="export LIBCLANG_PATH=\"$resolved_libclang_dir\""
else
  if ! ldconfig -p 2>/dev/null | grep -q 'libclang' \
     && [[ -z "${LIBCLANG_PATH:-}" ]] \
     && ! ls /usr/lib/llvm-*/lib/libclang.so* >/dev/null 2>&1; then
    LIBCLANG_DIR="$CACHE/libclang-$LIBCLANG_WHEEL_VERSION"
    if [[ ! -f "$LIBCLANG_DIR/libclang.so" ]]; then
      echo "downloading libclang $LIBCLANG_WHEEL_VERSION (python wheel) ..." >&2
      url="https://files.pythonhosted.org/packages/py2.py3/l/libclang/libclang-${LIBCLANG_WHEEL_VERSION}-py2.py3-none-manylinux2010_x86_64.whl"
      tmp="$(mktemp -d)"
      curl -fsSL -o "$tmp/libclang.whl" "$url"
      python3 -c "import zipfile,sys; zipfile.ZipFile(sys.argv[1]).extract('libclang-${LIBCLANG_WHEEL_VERSION}.data/platlib/clang/native/libclang.so', sys.argv[2])" "$tmp/libclang.whl" "$tmp"
      mkdir -p "$LIBCLANG_DIR"
      mv "$tmp/libclang-${LIBCLANG_WHEEL_VERSION}.data/platlib/clang/native/libclang.so" "$LIBCLANG_DIR/"
      rm -rf "$tmp"
    fi
    echo "libclang:  $LIBCLANG_DIR" >&2
    LIBCLANG_LINE="export LIBCLANG_PATH=\"$LIBCLANG_DIR\""

    # The libclang wheel ships no builtin headers (stddef.h, stdarg.h, ...). Point clang at the
    # system compiler's builtin include dir so bindgen can parse cvc5's headers.
    gcc_inc="$(dirname "$(gcc -print-file-name=include/stddef.h 2>/dev/null)" 2>/dev/null || true)"
    if [[ -n "$gcc_inc" && -f "$gcc_inc/stddef.h" ]]; then
      LIBCLANG_LINE="$LIBCLANG_LINE
export BINDGEN_EXTRA_CLANG_ARGS=\"\${BINDGEN_EXTRA_CLANG_ARGS:-} -I$gcc_inc\""
    fi
  else
    echo "libclang:  using system libclang" >&2
  fi
fi

# ---------------------------------------------------------------------------
# 3. Env file
# ---------------------------------------------------------------------------
cat > "$ENV_FILE" <<EOF
# generated by scripts/setup-cvc5-lib.sh — source this before building with --features cvc5-lib
export CVC5_LIB_DIR="$CVC5_DIR/lib"
export CVC5_INCLUDE_DIR="$CVC5_DIR/include"
$LIBCLANG_LINE
EOF

echo >&2
echo "wrote $ENV_FILE" >&2
echo "next:  source $ENV_FILE" >&2
