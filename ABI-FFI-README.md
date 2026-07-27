<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

# ABI / FFI — how GNPL reaches Lithoglyph

This repository follows the estate standard: **ABI defined in Idris2, FFI implemented in
Zig**, meeting at the C ABI. No C is written by hand.

> **History:** this file was previously the unfilled RSR template — 385 lines of
> `{{project}}` placeholders documenting an `ffi/zig/` tree that did not compile. It has
> been replaced with what the repository actually contains.

## The path

```
GNPL  ──lowers to──▶  GQLdt (Lean 4)
                          │
                          │ FFI: links -Lbridge/zig-out/lib -llith_bridge
                          ▼
                      bridge/ (Zig)  ── C ABI ──▶  Lithoglyph Form.Bridge
```

`lakefile.lean` links the Lean executables against `bridge/zig-out/lib/liblith_bridge.a`.
**That archive must exist before `lake build` runs.**

## Layout

| Path | Role |
|---|---|
| `src/GQLdt/ABI/Types.idr` | ABI type definitions |
| `src/GQLdt/ABI/Layout.idr` | memory-layout proofs |
| `src/GQLdt/ABI/Foreign.idr` | foreign declarations |
| `bridge/build.zig` | build script (`addLibrary`, Zig ≥ 0.15 API) |
| `bridge/lith_root.zig` | FFI entry point — the exported C surface |
| `bridge/lith_types.zig` | C-ABI structs (`ActorIdC`, `RationaleC`, `ProvenanceC`, `TrackedValueC`, `ProofBlob`, `PromptScoresC`) |
| `bridge/lith_insert.zig`, `bridge/lith_persist.zig` | insert + persistence implementation |

`bridge/` is the **only** live Zig tree. Two earlier skeletons (`bridge/zig/`, `ffi/zig/`)
were removed — they were written against the pre-0.15 Build API (`addStaticLibrary`,
`std.heap.GeneralPurposeAllocator`), failed to compile on the pinned Zig 0.16.0, and nothing
linked against them.

## Building

```bash
cd bridge
zig build                          # produces zig-out/lib/liblith_bridge.a
zig build test                     # unit tests
zig build -Doptimize=ReleaseFast   # optimised
```

Cross-compilation works as usual (`-Dtarget=aarch64-macos`, etc.).

Then, from the repository root:

```bash
lake build
```

Zig is pinned to **0.16.0** in `mise.toml`. Lean is pinned by `lean-toolchain`
(`leanprover/lean4:v4.15.0`), which elan reads automatically.

## Exported C surface

Seventeen functions, all `callconv(.C)`, from `bridge/`:

**Lifecycle** — `lith_init`, `lith_is_init`, `lith_close`, `lith_save`
**Data** — `lith_insert`, `lith_insert_row`, `lith_delete_row`, `lith_table_count`
**PROMPT scores** — `lith_get_scores`, `lith_compute_overall`
**Proofs** — `lith_verify_proof`
**Utility** — `lith_validate_non_empty`, `lith_timestamp_now`, `lith_get_last_error`
**Debug/test** — `lith_debug_init_counter`, `lith_debug_magic`, `lith_test_fresh`

Provenance crosses the boundary as real structs, not opaque blobs: `ActorIdC`,
`RationaleC`, `ProvenanceC` and `TrackedValueC` are marshalled directly. This is what makes
the GNPL narration layer buildable over this stack — see `docs/LITHOGLYPH.adoc`.

> **Caveat.** `PromptScoresC.computeOverall` takes an **unweighted mean** of the six PROMPT
> dimensions. It is not probabilistically principled, and must not become a load-bearing
> entrenchment ordering without being revisited — see open question 2 in `docs/THEORY.adoc`.

## Why this split

**Idris2 for the ABI** — dependent types let struct size, field alignment and cross-version
compatibility be *proved* rather than asserted, so an ABI change that would break a caller
fails at compile time.

**Zig for the FFI** — `export fn … callconv(.C)` is C-compatible without a C compiler,
without libc, and with cross-compilation built in.

## Adding a function

1. Declare the type in `src/GQLdt/ABI/Types.idr`; add a layout proof in `Layout.idr`.
2. Declare it in `src/GQLdt/ABI/Foreign.idr`.
3. Implement and `export` it in `bridge/` (match the ABI types exactly).
4. `cd bridge && zig build && zig build test`, then `lake build` from the root.

## Related

- `docs/THEORY.adoc` — what GNPL is, and what gap it fills
- `docs/LITHOGLYPH.adoc` — what GNPL gives Lithoglyph as a database
- `docs/proof-debt.md` — the 16 outstanding axioms; **read before relying on any
  verification claim**
