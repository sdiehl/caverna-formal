# caverna

Formal proof that **furnishing rush** is the unique weakly dominant strategy in 2-player Caverna.

[Blueprint](https://sdiehl.github.io/caverna-formal/blueprint/)

## Install

```
# lean
brew install elan-init
elan toolchain install leanprover/lean4:v4.28.0

# blueprint deps
brew install graphviz
curl -LsSf https://astral.sh/uv/install.sh | sh
uv tool install leanblueprint
```

## Build

```
lake exe cache get   # fetch mathlib cache (~5 min first time)
lake build           # build project
```

## Blueprint

```
leanblueprint web    # compile HTML + dependency graph
leanblueprint serve  # http://localhost:8000
```

## Verify

```
lake exe checkdecls blueprint/lean_decls
```
