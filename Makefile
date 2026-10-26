# Sky on Cairn. Everything goes through Cairn's `cairn` CLI (cairn's docs/cli.md), built from
# the Cairn checkout Lake fetched from the registry (lean/.lake/packages/cairn).

export PATH := $(HOME)/.elan/bin:$(PATH)
export RESERVOIR_API_URL := https://cairn.registry.nexthub.sh/api/v1
CAIRN_PKG = lean/.lake/packages/cairn
CAIRN = $(CAIRN_PKG)/tools/cairn/.build/release/cairn

.PHONY: deps cairn-tool build app selftest bench bench-lean lean lint audit ledger ledger-update kernel fuzz size claims check clean

# Fetch Cairn, cairn_json and cairn_atproto as lean/lake-manifest.json pins them.
deps:
	cd lean && lake env true

# The `cairn` CLI from the fetched Cairn.
cairn-tool: deps
	swift build -c release --package-path $(CAIRN_PKG)/tools/cairn

# lake build, cairn-link into .cairn/lib/libsky.a, swift build.
build: cairn-tool
	$(CAIRN) build

# Sky.app, built for release by `cairn bundle` (bundle/Info.plist; bundle/entitlements.plist is
# empty and only turns on the hardened runtime), signed and installed in ~/Applications. SIGN is
# a codesign identity: the first "Developer ID Application" one in the keychain, else `-`.
SIGN ?= $(or $(shell security find-identity -v -p codesigning 2>/dev/null | grep -m1 '"Developer ID Application' | sed -E 's/.*"(.*)"/\1/'),-)
app: build
	$(CAIRN) bundle --product Sky --sign "$(SIGN)"
	rm -rf $(HOME)/Applications/Sky.app
	mkdir -p $(HOME)/Applications
	ditto build/apps/Sky.app $(HOME)/Applications/Sky.app
	@echo "sky: installed ~/Applications/Sky.app, signed $(if $(filter -,$(SIGN)),ad hoc (no Developer ID identity),by $(SIGN))"

# The headless check runs with a home of its own (build/home), so it never reads a saved service
# or touches the network.
HOME_TEST = $(CURDIR)/build/home
# cairn_atproto's fake PDS (Bun), which the selftest runs on 127.0.0.1 and stops.
FAKE_PDS = lean/.lake/packages/cairn_atproto/tools/fake-pds/server.ts

selftest: build
	rm -rf $(HOME_TEST) && mkdir -p $(HOME_TEST) && CFFIXED_USER_HOME=$(HOME_TEST) swift run Sky --selftest $(FAKE_PDS) --shots build/shots

# bench/README.md: `cairn bench` (a release build, then `Sky --bench` against the fake PDS, with a
# home of its own like the selftest's), and Sky's frames by phase in Lean (`lake exe bench`).
HOME_BENCH = $(CURDIR)/build/home-bench
bench: cairn-tool
	rm -rf $(HOME_BENCH) && mkdir -p $(HOME_BENCH) && CFFIXED_USER_HOME=$(HOME_BENCH) $(CAIRN) bench

bench-lean:
	cd lean && LAKE_ARTIFACT_CACHE=false lake build bench && LEAN_ABORT_ON_NONLINEAR=1 .lake/build/bin/bench

# The Lean side alone. `cairn build` turns Lake's artifact cache on, which keeps .olean files out
# of the build directory, and the ledger and audit import from there: turn it off.
lean:
	cd lean && LAKE_ARTIFACT_CACHE=false lake build -q

# Constructs that bypass the kernel or swap in unchecked code (AGENTS.md, Rules).
lint:
	@! grep -rnE 'implemented_by|skipKernelTC|native_decide|bv_decide|^\s*axiom |\bsorry\b' lean/Sky lean/*.lean \
	  || (echo "lint: forbidden construct (see AGENTS.md, Rules)"; exit 1)

# Every theorem depends only on propext, Classical.choice and Quot.sound.
audit: lean
	cd lean && lake exe audit Checks Sky

# Every sky^N claim is in claims.lock with its statement hash; `ledger-update` writes new ones.
ledger: lean
	cd lean && lake exe ledger check --scope sky --root Checks --lock ../claims.lock

ledger-update: lean
	cd lean && lake exe ledger update --scope sky --root Checks --lock ../claims.lock

# Replay every declaration through the kernel (unsandboxed: macOS has no bubblewrap).
kernel: lean
	cd lean && lake check --inadvisably-no-sandbox

# Cairn's fuzzer on the app through the runtime, with a simulated host and Sky's fake server
# (`Sky.fuzz`, lean/Sky/Fuzz.lean): replies late, in any order, failing, to cancelled and stray
# ids; tokens expiring; new posts at the head. Into build/fuzz/Claims.json.
FUZZ_ITERATIONS ?= 200
FUZZ_STEPS ?= 300
fuzz: cairn-tool
	$(CAIRN) fuzz --iterations $(FUZZ_ITERATIONS) --steps $(FUZZ_STEPS)

# The release binary's size, attributed (build/size/), under Cairn's 5 MB limit.
size: cairn-tool
	$(CAIRN) size

# Every claim as the registry will show it (build/claims.json).
claims: cairn-tool
	mkdir -p build
	$(CAIRN) claims --ledger --out build/claims.json

check: build lint audit ledger kernel selftest fuzz size claims

clean:
	rm -rf build .cairn .build lean/.lake
