# Caverna formal proof project
# Lean 4 + Mathlib + LeanBlueprint

# Default: build lean
default: build

# ── Setup ──────────────────────────────────────────────

# Install all dependencies (macOS)
setup:
    brew install graphviz elan just
    elan install leanprover/lean4:v4.18.0
    lake update

# Install blueprint tooling
setup-blueprint:
    CFLAGS="-I$(brew --prefix graphviz)/include" \
    LDFLAGS="-L$(brew --prefix graphviz)/lib" \
    uv tool install leanblueprint --with pygraphviz

# ── Build ──────────────────────────────────────────────

# Build the Lean project
build:
    lake build

# Build with clean slate
clean-build:
    lake clean
    lake build

# ── Check ──────────────────────────────────────────────

# Verify blueprint declarations match Lean
checkdecls:
    lake exe checkdecls blueprint/lean_decls

# Run all checks (build + checkdecls)
check: build checkdecls

# ── Blueprint ──────────────────────────────────────────

# Build blueprint web output
blueprint-web:
    CFLAGS="-I$(brew --prefix graphviz)/include" \
    LDFLAGS="-L$(brew --prefix graphviz)/lib" \
    leanblueprint web

# Build blueprint PDF
blueprint-pdf:
    CFLAGS="-I$(brew --prefix graphviz)/include" \
    LDFLAGS="-L$(brew --prefix graphviz)/lib" \
    leanblueprint pdf

# Build both blueprint outputs
blueprint: blueprint-web blueprint-pdf

# Serve blueprint locally for preview
blueprint-serve:
    cd blueprint/web && python3 -m http.server 8080

# ── Full pipeline ──────────────────────────────────────

# Build everything: lean + checkdecls + blueprint
all: check blueprint

# ── Clean ──────────────────────────────────────────────

# Clean Lean build artifacts
clean:
    lake clean

# Clean blueprint outputs
clean-blueprint:
    rm -rf blueprint/web blueprint/print
