# OpenMLS — extraction targets
#
#   make extract         hax → Lean (uses $(INCLUDE),         logs to $(HAX_OUTPUT))
#   make extract-charon  charon → LLBC (uses $(INCLUDE_CHARON), logs to $(CHARON_OUTPUT),
#                                       artifact at $(LLBC_OUTPUT))
#
# Both filters mirror the same eight extraction units from `../extraction.org`.
# Edit either INCLUDE list to carve out FV-irrelevant items.
#
# Run from the workspace root (this directory).

# Use bash with pipefail so `make` notices hax failures even though we tee
# through a pipe (sh's default would mask them).
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

CRATE_DIR     := openmls
HAX_OUTPUT    := /tmp/hax_output
LLBC_OUTPUT   := openmls.llbc
CHARON_OUTPUT := /tmp/charon_output

# ----- Currently active extraction filter -----------------------------------
INCLUDE := -**

# --- Toolchain pilots (already extracted) ---
INCLUDE += +openmls::ciphersuite::aead::**
INCLUDE += +openmls::ciphersuite::secret::**

# --- The eight FV-target units (priority order matches extraction.org) ---

# 1. skip_validation                       (FV #5, smallest pilot)
INCLUDE += +openmls::skip_validation::**

# 2 + 3. public_group::{validation, mod, process, staged_commit}
#   #2 covers FV #1, #2 (mod.rs hook), #6; #3 covers FV #6.
#   Carve out builder/diff/errors (substrate, not on the FV path).
INCLUDE += +openmls::group::public_group::**
INCLUDE += -openmls::group::public_group::builder::**
INCLUDE += -openmls::group::public_group::diff::**
INCLUDE += -openmls::group::public_group::errors::**

# 4. mls_group::commit_builder::external_commits  (FV #6 — sender side, H-4)
# Commented out: 4 errors (HAX0003/HAX0010) at L300-302. See extraction.org.
# INCLUDE += +openmls::group::mls_group::commit_builder::external_commits::**

# 5. key_packages::{mod, key_package_in, lifetime}  (FV #1)
#   Carve out errors (substrate).
INCLUDE += +openmls::key_packages::**
INCLUDE += -openmls::key_packages::errors::**

# 6. treesync::node::{leaf_node, parent_node, codec, encryption_keys}
#    (FV #1, #3, #7) — full tree-node ADT in one unit.
INCLUDE += +openmls::treesync::node::**

# 7. mls_group::creation                   (FV #2 — Welcome typestate)
INCLUDE += +openmls::group::mls_group::creation::**

# 8. treesync::{diff, hashes}              (FV #3, #8 — parent-hash + atomicity)
# Commented out: 39 errors in treesync/diff (29× HAX0002 "type Dyn with non
# trait predicate" plus HAX0003/0010/0008 cluster). See extraction.org.
# INCLUDE += +openmls::treesync::diff::**
# INCLUDE += +openmls::treesync::hashes::**

# ----- Charon extraction filter --------------------------------------------
# `--start-from <path>` sets a translation entry point: charon translates
# the named item AND items it references (transitive closure), and never
# visits items unreachable from the starting set. This is the analog of
# hax's `+module::**` (item + transitive deps). `--exclude` blacklists
# specific items even if reachable, mirroring hax's `-`.

INCLUDE_CHARON :=

# --- Toolchain pilots ---
INCLUDE_CHARON += --start-from 'openmls::ciphersuite::aead'
INCLUDE_CHARON += --start-from 'openmls::ciphersuite::secret'

# --- The eight FV-target units (mirrors INCLUDE above) ---

# 1. skip_validation
INCLUDE_CHARON += --start-from 'openmls::skip_validation'

# 2 + 3. public_group::{validation, mod, process, staged_commit}
INCLUDE_CHARON += --start-from 'openmls::group::public_group'
INCLUDE_CHARON += --exclude 'openmls::group::public_group::builder'
INCLUDE_CHARON += --exclude 'openmls::group::public_group::diff'
INCLUDE_CHARON += --exclude 'openmls::group::public_group::errors'

# 4. external_commits
INCLUDE_CHARON += --start-from 'openmls::group::mls_group::commit_builder::external_commits'

# 5. key_packages::{mod, key_package_in, lifetime}
INCLUDE_CHARON += --start-from 'openmls::key_packages'
INCLUDE_CHARON += --exclude 'openmls::key_packages::errors'

# 6. treesync::node::{leaf_node, parent_node, codec, encryption_keys}
INCLUDE_CHARON += --start-from 'openmls::treesync::node'

# 7. mls_group::creation
INCLUDE_CHARON += --start-from 'openmls::group::mls_group::creation'

# 8. treesync::{diff, hashes}
INCLUDE_CHARON += --start-from 'openmls::treesync::diff'
INCLUDE_CHARON += --start-from 'openmls::treesync::hashes'

# 9. extra flags
INCLUDE_CHARON += --include 'openmls::group::public_group::errors::PublicGroupBuildError'
INCLUDE_CHARON += --include 'openmls::group::public_group::diff::compute_path::CommitType'

# ============================================================================
# Per-FV-target standalone recipes
# ============================================================================
# Each target gets a triple of recipes following the same convention:
#   extract-<short>   charon  → LLBC          (artifact: <short>.llbc,    log: <short>_charon.log)
#   hax-<short>       hax     → Lean (direct) (log: <short>_hax.log)
#   aeneas-<short>    hax     → aeneas → Lean (log: <short>_aeneas.log; artefacts in proofs/aeneas-lean/)
# All commands cd into $(CRATE_DIR); outputs land in that directory.
#
# Short name → FV target (per wip.org; skipped: [4] tls_codec external, [10] symbolic):
#   treemath   [12] Tree-math panic-freedom
#   parenthash [3]  Parent-hash chain
#   valid      [1]  Validator completeness
#   welcome    [2]  Welcome typestate
#   skipval    [5]  Bypass-path unreachability
#   extcommit  [6]  External-commit allowlist
#   tbs        [7]  Signature-TBS context exhaustiveness
#   mutatomic  [8]  State-mutation atomicity (narrow on diff.rs)
#   zeroize    [9]  Memory-hygiene typestate
#   reinit     [11] ReInit rejection
#   sigkey     [13] CommitBuilder sig-key uniqueness
#   kpsig      [14] CommitBuilder KP signatures
#   respsk     [15] Resumption PSK identity binding
#
# Note: charon's --start-from is item-based (mod.rs items + transitive deps);
# hax's +module::** also pulls in all submodules. The asymmetry means hax
# filters may extract a wider surface than charon for the same target.

# Common aeneas-pipeline excludes — serde derives confuse the aeneas backend.
AENEAS_EXCLUDES := \
	--exclude '{impl serde_core::ser::Serialize for _}' \
	--exclude '{impl serde_core::de::Deserialize for _}'

# ----- [12] treemath --------------------------------------------------------
TREEMATH_LLBC   := treemath.llbc
TREEMATH_CHARON := treemath_charon.log
TREEMATH_HAX    := treemath_hax.log
TREEMATH_AENEAS := treemath_aeneas.log

# ----- [3] parenthash -------------------------------------------------------
# Files: treesync/{diff,hashes}.rs, treesync/node/parent_node.rs.
# Known status (extraction.org §unit 8): hax partial (39 errors, dominated by
# HAX0002 dyn-trait helpers in diff.rs); charon partial (6 errors in diff.rs).
PARENTHASH_LLBC   := parenthash.llbc
PARENTHASH_CHARON := parenthash_charon.log
PARENTHASH_HAX    := parenthash_hax.log
PARENTHASH_AENEAS := parenthash_aeneas.log

# ----- [1] valid (validator completeness) ----------------------------------
# Files: group/public_group/validation.rs, key_packages/key_package_in.rs,
#        treesync/node/leaf_node.rs, key_packages/lifetime.rs
VALID_LLBC   := valid.llbc
VALID_CHARON := valid_charon.log
VALID_HAX    := valid_hax.log
VALID_AENEAS := valid_aeneas.log

# ----- [2] welcome (Welcome typestate) -------------------------------------
# Files: group/mls_group/creation.rs, messages/group_info.rs
#        (messages/mod.rs and public_group/mod.rs pulled transitively)
WELCOME_LLBC   := welcome.llbc
WELCOME_CHARON := welcome_charon.log
WELCOME_HAX    := welcome_hax.log
WELCOME_AENEAS := welcome_aeneas.log

# ----- [5] skipval (bypass-path unreachability) ----------------------------
SKIPVAL_LLBC   := skipval.llbc
SKIPVAL_CHARON := skipval_charon.log
SKIPVAL_HAX    := skipval_hax.log
SKIPVAL_AENEAS := skipval_aeneas.log

# ----- [6] extcommit (external-commit allowlist) ---------------------------
# Files: public_group/{validation,staged_commit}.rs,
#        mls_group/commit_builder/external_commits.rs
EXTCOMMIT_LLBC   := extcommit.llbc
EXTCOMMIT_CHARON := extcommit_charon.log
EXTCOMMIT_HAX    := extcommit_hax.log
EXTCOMMIT_AENEAS := extcommit_aeneas.log

# ----- [7] tbs (signature-TBS context exhaustiveness) ----------------------
# Files: framing/mls_content.rs, treesync/node/leaf_node.rs, messages/group_info.rs
TBS_LLBC   := tbs.llbc
TBS_CHARON := tbs_charon.log
TBS_HAX    := tbs_hax.log
TBS_AENEAS := tbs_aeneas.log

# ----- [8] mutatomic (state-mutation atomicity) ----------------------------
# Narrow scope on treesync/diff.rs (apply_received_update_path).
MUTATOMIC_LLBC   := mutatomic.llbc
MUTATOMIC_CHARON := mutatomic_charon.log
MUTATOMIC_HAX    := mutatomic_hax.log
MUTATOMIC_AENEAS := mutatomic_aeneas.log

# ----- [9] zeroize (memory-hygiene typestate) ------------------------------
# Files: ciphersuite/aead.rs, ciphersuite/secret.rs, schedule/mod.rs
ZEROIZE_LLBC   := zeroize.llbc
ZEROIZE_CHARON := zeroize_charon.log
ZEROIZE_HAX    := zeroize_hax.log
ZEROIZE_AENEAS := zeroize_aeneas.log

# ----- [11] reinit (ReInit rejection) --------------------------------------
# Files: mls_group/{proposal_store,proposal}.rs, public_group/validation.rs
REINIT_LLBC   := reinit.llbc
REINIT_CHARON := reinit_charon.log
REINIT_HAX    := reinit_hax.log
REINIT_AENEAS := reinit_aeneas.log

# ----- [13] sigkey (CommitBuilder sig-key uniqueness) -----------------------
# Files: mls_group/commit_builder.rs, public_group/validation.rs
SIGKEY_LLBC   := sigkey.llbc
SIGKEY_CHARON := sigkey_charon.log
SIGKEY_HAX    := sigkey_hax.log
SIGKEY_AENEAS := sigkey_aeneas.log

# ----- [14] kpsig (CommitBuilder KP signatures) -----------------------------
# Files: mls_group/commit_builder.rs, ciphersuite/signable.rs
KPSIG_LLBC   := kpsig.llbc
KPSIG_CHARON := kpsig_charon.log
KPSIG_HAX    := kpsig_hax.log
KPSIG_AENEAS := kpsig_aeneas.log

# ----- [15] respsk (resumption PSK identity binding) ------------------------
RESPSK_LLBC   := respsk.llbc
RESPSK_CHARON := respsk_charon.log
RESPSK_HAX    := respsk_hax.log
RESPSK_AENEAS := respsk_aeneas.log

# ----- PHONY ---------------------------------------------------------------
.PHONY: extract extract-charon help \
	extract-treemath hax-treemath aeneas-treemath \
	extract-parenthash hax-parenthash aeneas-parenthash \
	extract-valid hax-valid aeneas-valid \
	extract-welcome hax-welcome aeneas-welcome \
	extract-skipval hax-skipval aeneas-skipval \
	extract-extcommit hax-extcommit aeneas-extcommit \
	extract-tbs hax-tbs aeneas-tbs \
	extract-mutatomic hax-mutatomic aeneas-mutatomic \
	extract-zeroize hax-zeroize aeneas-zeroize \
	extract-reinit hax-reinit aeneas-reinit \
	extract-sigkey hax-sigkey aeneas-sigkey \
	extract-kpsig hax-kpsig aeneas-kpsig \
	extract-respsk hax-respsk aeneas-respsk \
	extract-all-fv hax-all-fv aeneas-all-fv \
	module-all-charon module-status-charon module-combined-charon \
	module-fullcrate-charon \
	$(MODULE_TARGETS)

# ----- Umbrella recipes (full INCLUDE / INCLUDE_CHARON filters) ------------

extract:
	@echo "==> extract (output: $(HAX_OUTPUT))"
	@cd $(CRATE_DIR) && cargo hax into -i '$(strip $(INCLUDE))' lean 2>&1 | tee $(HAX_OUTPUT)

extract-charon:
	@echo "==> extract-charon (llbc: $(LLBC_OUTPUT), log: $(CHARON_OUTPUT))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas $(INCLUDE_CHARON) --dest-file $(LLBC_OUTPUT) 2>&1 | tee $(CHARON_OUTPUT)

# ----- [12] treemath recipes -----------------------------------------------

extract-treemath:
	@echo "==> extract-treemath (llbc: $(TREEMATH_LLBC), log: $(TREEMATH_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::binary_tree::array_representation::treemath' \
		$(AENEAS_EXCLUDES) \
		--dest-file $(TREEMATH_LLBC) 2>&1 | tee $(TREEMATH_CHARON)

hax-treemath:
	@echo "==> hax-treemath (log: $(TREEMATH_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::binary_tree::array_representation::treemath::**' \
		lean 2>&1 | tee $(TREEMATH_HAX)

aeneas-treemath:
	@echo "==> aeneas-treemath (log: $(TREEMATH_AENEAS))"
	@cd $(CRATE_DIR) && \
		cargo hax into -v aeneas-lean \
		--charon-args=" \
			--start-from 'openmls::binary_tree::array_representation::treemath' \
			$(AENEAS_EXCLUDES) \
			--exclude '{impl core::fmt::Debug for _}' \
			--exclude '{impl core::fmt::Display for _}' \
			--exclude '{impl tls_codec::Size for _}' \
			--exclude '{impl tls_codec::Serialize for _}' \
			--exclude '{impl tls_codec::Deserialize for _}' \
			--exclude '{impl tls_codec::DeserializeBytes for _}'" \
		--aeneas-args="-core-models-lib" \
		2>&1 | tee $(TREEMATH_AENEAS)

# ----- [3] parenthash recipes ----------------------------------------------

extract-parenthash:
	@echo "==> extract-parenthash (llbc: $(PARENTHASH_LLBC), log: $(PARENTHASH_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::diff' \
		--start-from 'openmls::treesync::hashes' \
		--start-from 'openmls::treesync::node::parent_node' \
		--dest-file $(PARENTHASH_LLBC) 2>&1 | tee $(PARENTHASH_CHARON)

hax-parenthash:
	@echo "==> hax-parenthash (log: $(PARENTHASH_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::treesync::diff::** +openmls::treesync::hashes::** +openmls::treesync::node::parent_node::**' \
		lean 2>&1 | tee $(PARENTHASH_HAX)

aeneas-parenthash:
	@echo "==> aeneas-parenthash (log: $(PARENTHASH_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::treesync::diff' \
			--start-from 'openmls::treesync::hashes' \
			--start-from 'openmls::treesync::node::parent_node' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(PARENTHASH_AENEAS)

# ----- [1] valid recipes ---------------------------------------------------

extract-valid:
	@echo "==> extract-valid (llbc: $(VALID_LLBC), log: $(VALID_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::validation' \
		--start-from 'openmls::key_packages::key_package_in' \
		--start-from 'openmls::treesync::node::leaf_node' \
		--start-from 'openmls::key_packages::lifetime' \
		--dest-file $(VALID_LLBC) 2>&1 | tee $(VALID_CHARON)

hax-valid:
	@echo "==> hax-valid (log: $(VALID_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::group::public_group::validation::** +openmls::key_packages::key_package_in::** +openmls::treesync::node::leaf_node::** +openmls::key_packages::lifetime::**' \
		lean 2>&1 | tee $(VALID_HAX)

aeneas-valid:
	@echo "==> aeneas-valid (log: $(VALID_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::group::public_group::validation' \
			--start-from 'openmls::key_packages::key_package_in' \
			--start-from 'openmls::treesync::node::leaf_node' \
			--start-from 'openmls::key_packages::lifetime' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(VALID_AENEAS)

# ----- [2] welcome recipes -------------------------------------------------

extract-welcome:
	@echo "==> extract-welcome (llbc: $(WELCOME_LLBC), log: $(WELCOME_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::creation' \
		--start-from 'openmls::messages::group_info' \
		--dest-file $(WELCOME_LLBC) 2>&1 | tee $(WELCOME_CHARON)

hax-welcome:
	@echo "==> hax-welcome (log: $(WELCOME_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::group::mls_group::creation::** +openmls::messages::group_info::**' \
		lean 2>&1 | tee $(WELCOME_HAX)

aeneas-welcome:
	@echo "==> aeneas-welcome (log: $(WELCOME_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::group::mls_group::creation' \
			--start-from 'openmls::messages::group_info' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(WELCOME_AENEAS)

# ----- [5] skipval recipes -------------------------------------------------

extract-skipval:
	@echo "==> extract-skipval (llbc: $(SKIPVAL_LLBC), log: $(SKIPVAL_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::skip_validation' \
		--dest-file $(SKIPVAL_LLBC) 2>&1 | tee $(SKIPVAL_CHARON)

hax-skipval:
	@echo "==> hax-skipval (log: $(SKIPVAL_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::skip_validation::**' \
		lean 2>&1 | tee $(SKIPVAL_HAX)

aeneas-skipval:
	@echo "==> aeneas-skipval (log: $(SKIPVAL_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::skip_validation' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(SKIPVAL_AENEAS)

# ----- [6] extcommit recipes -----------------------------------------------

extract-extcommit:
	@echo "==> extract-extcommit (llbc: $(EXTCOMMIT_LLBC), log: $(EXTCOMMIT_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::validation' \
		--start-from 'openmls::group::public_group::staged_commit' \
		--start-from 'openmls::group::mls_group::commit_builder::external_commits' \
		--dest-file $(EXTCOMMIT_LLBC) 2>&1 | tee $(EXTCOMMIT_CHARON)

hax-extcommit:
	@echo "==> hax-extcommit (log: $(EXTCOMMIT_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::group::public_group::validation::** +openmls::group::public_group::staged_commit::** +openmls::group::mls_group::commit_builder::external_commits::**' \
		lean 2>&1 | tee $(EXTCOMMIT_HAX)

aeneas-extcommit:
	@echo "==> aeneas-extcommit (log: $(EXTCOMMIT_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::group::public_group::validation' \
			--start-from 'openmls::group::public_group::staged_commit' \
			--start-from 'openmls::group::mls_group::commit_builder::external_commits' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(EXTCOMMIT_AENEAS)

# ----- [7] tbs recipes -----------------------------------------------------

extract-tbs:
	@echo "==> extract-tbs (llbc: $(TBS_LLBC), log: $(TBS_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::mls_content' \
		--start-from 'openmls::treesync::node::leaf_node' \
		--start-from 'openmls::messages::group_info' \
		--dest-file $(TBS_LLBC) 2>&1 | tee $(TBS_CHARON)

hax-tbs:
	@echo "==> hax-tbs (log: $(TBS_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::framing::mls_content::** +openmls::treesync::node::leaf_node::** +openmls::messages::group_info::**' \
		lean 2>&1 | tee $(TBS_HAX)

aeneas-tbs:
	@echo "==> aeneas-tbs (log: $(TBS_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::framing::mls_content' \
			--start-from 'openmls::treesync::node::leaf_node' \
			--start-from 'openmls::messages::group_info' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(TBS_AENEAS)

# ----- [8] mutatomic recipes -----------------------------------------------

extract-mutatomic:
	@echo "==> extract-mutatomic (llbc: $(MUTATOMIC_LLBC), log: $(MUTATOMIC_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::diff' \
		--dest-file $(MUTATOMIC_LLBC) 2>&1 | tee $(MUTATOMIC_CHARON)

hax-mutatomic:
	@echo "==> hax-mutatomic (log: $(MUTATOMIC_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::treesync::diff::**' \
		lean 2>&1 | tee $(MUTATOMIC_HAX)

aeneas-mutatomic:
	@echo "==> aeneas-mutatomic (log: $(MUTATOMIC_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::treesync::diff' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(MUTATOMIC_AENEAS)

# ----- [9] zeroize recipes -------------------------------------------------

extract-zeroize:
	@echo "==> extract-zeroize (llbc: $(ZEROIZE_LLBC), log: $(ZEROIZE_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::aead' \
		--start-from 'openmls::ciphersuite::secret' \
		--start-from 'openmls::schedule' \
		--dest-file $(ZEROIZE_LLBC) 2>&1 | tee $(ZEROIZE_CHARON)

hax-zeroize:
	@echo "==> hax-zeroize (log: $(ZEROIZE_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::ciphersuite::aead::** +openmls::ciphersuite::secret::** +openmls::schedule::**' \
		lean 2>&1 | tee $(ZEROIZE_HAX)

aeneas-zeroize:
	@echo "==> aeneas-zeroize (log: $(ZEROIZE_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::ciphersuite::aead' \
			--start-from 'openmls::ciphersuite::secret' \
			--start-from 'openmls::schedule' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(ZEROIZE_AENEAS)

# ----- [11] reinit recipes -------------------------------------------------

extract-reinit:
	@echo "==> extract-reinit (llbc: $(REINIT_LLBC), log: $(REINIT_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::proposal_store' \
		--start-from 'openmls::group::mls_group::proposal' \
		--start-from 'openmls::group::public_group::validation' \
		--dest-file $(REINIT_LLBC) 2>&1 | tee $(REINIT_CHARON)

hax-reinit:
	@echo "==> hax-reinit (log: $(REINIT_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::group::mls_group::proposal_store::** +openmls::group::mls_group::proposal::** +openmls::group::public_group::validation::**' \
		lean 2>&1 | tee $(REINIT_HAX)

aeneas-reinit:
	@echo "==> aeneas-reinit (log: $(REINIT_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::group::mls_group::proposal_store' \
			--start-from 'openmls::group::mls_group::proposal' \
			--start-from 'openmls::group::public_group::validation' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(REINIT_AENEAS)

# ----- [13] sigkey recipes -------------------------------------------------

extract-sigkey:
	@echo "==> extract-sigkey (llbc: $(SIGKEY_LLBC), log: $(SIGKEY_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::commit_builder' \
		--start-from 'openmls::group::public_group::validation' \
		--dest-file $(SIGKEY_LLBC) 2>&1 | tee $(SIGKEY_CHARON)

hax-sigkey:
	@echo "==> hax-sigkey (log: $(SIGKEY_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::group::mls_group::commit_builder::** +openmls::group::public_group::validation::**' \
		lean 2>&1 | tee $(SIGKEY_HAX)

aeneas-sigkey:
	@echo "==> aeneas-sigkey (log: $(SIGKEY_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::group::mls_group::commit_builder' \
			--start-from 'openmls::group::public_group::validation' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(SIGKEY_AENEAS)

# ----- [14] kpsig recipes --------------------------------------------------

extract-kpsig:
	@echo "==> extract-kpsig (llbc: $(KPSIG_LLBC), log: $(KPSIG_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::commit_builder' \
		--start-from 'openmls::ciphersuite::signable' \
		--dest-file $(KPSIG_LLBC) 2>&1 | tee $(KPSIG_CHARON)

hax-kpsig:
	@echo "==> hax-kpsig (log: $(KPSIG_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::group::mls_group::commit_builder::** +openmls::ciphersuite::signable::**' \
		lean 2>&1 | tee $(KPSIG_HAX)

aeneas-kpsig:
	@echo "==> aeneas-kpsig (log: $(KPSIG_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::group::mls_group::commit_builder' \
			--start-from 'openmls::ciphersuite::signable' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(KPSIG_AENEAS)

# ----- [15] respsk recipes -------------------------------------------------

extract-respsk:
	@echo "==> extract-respsk (llbc: $(RESPSK_LLBC), log: $(RESPSK_CHARON))"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::schedule::psk' \
		--dest-file $(RESPSK_LLBC) 2>&1 | tee $(RESPSK_CHARON)

hax-respsk:
	@echo "==> hax-respsk (log: $(RESPSK_HAX))"
	@cd $(CRATE_DIR) && cargo hax into \
		-i '-** +openmls::schedule::psk::**' \
		lean 2>&1 | tee $(RESPSK_HAX)

aeneas-respsk:
	@echo "==> aeneas-respsk (log: $(RESPSK_AENEAS))"
	@cd $(CRATE_DIR) && cargo hax into aeneas-lean \
		--lakefile \
		--charon-args=" \
			--start-from 'openmls::schedule::psk' \
			$(AENEAS_EXCLUDES)" \
		2>&1 | tee $(RESPSK_AENEAS)

# ----- Bulk recipes --------------------------------------------------------

EXTRACT_FV_TARGETS := extract-treemath extract-parenthash extract-valid extract-welcome \
                      extract-skipval extract-extcommit extract-tbs extract-mutatomic \
                      extract-zeroize extract-reinit extract-sigkey extract-kpsig extract-respsk

HAX_FV_TARGETS := hax-treemath hax-parenthash hax-valid hax-welcome \
                  hax-skipval hax-extcommit hax-tbs hax-mutatomic \
                  hax-zeroize hax-reinit hax-sigkey hax-kpsig hax-respsk

AENEAS_FV_TARGETS := aeneas-treemath aeneas-parenthash aeneas-valid aeneas-welcome \
                     aeneas-skipval aeneas-extcommit aeneas-tbs aeneas-mutatomic \
                     aeneas-zeroize aeneas-reinit aeneas-sigkey aeneas-kpsig aeneas-respsk

extract-all-fv: $(EXTRACT_FV_TARGETS)
hax-all-fv:     $(HAX_FV_TARGETS)
aeneas-all-fv:  $(AENEAS_FV_TARGETS)

# ============================================================================
# Per-module charon extraction sweep
# ============================================================================
# Independent of the FV-target recipes above. Goal: one LLBC per substantive
# source file under src/, with each LLBC isolated to that file's items.
#
# Opacity-confinement pattern (per charon/dev/docs/what_charon_translates.md):
#
#   --start-from 'openmls::P'    work-queue entry point
#   --opaque    'openmls::_'     every openmls item: signature-only by default
#   --include   'openmls::P'     re-open the target back to Transparent
#
# Precedence rule (longer pattern wins; non-glob beats glob of equal length)
# makes openmls::P Transparent for P and all its descendants, while sibling
# modules stay Opaque. Foreign items (std, tls_codec, core, ...) are
# unaffected. Result: each per-module LLBC is small and isolated.
#
# On top of the confinement, we drop the four trait-impl categories the
# verification work doesn't care about — Serialize, Deserialize, Debug,
# Display — which together account for most of the aeneas-side errors in
# session_020626's digest.

MODULE_EXCLUDES := \
	--exclude '{impl serde_core::ser::Serialize for _}' \
	--exclude '{impl serde_core::de::Deserialize for _}' \
	--exclude '{impl std::fmt::Debug for _}' \
	--exclude '{impl std::fmt::Display for _}'

# Canned recipe: $(call module_recipe,<short>,<module::path>)
# Spelled out without `define` to keep each rule self-contained at the call site.
# Each rule writes LLBC to the workspace root (parent of $(CRATE_DIR)) and log
# into $(CRATE_DIR), matching the FV-recipe convention.

# ----- binary_tree/array_representation/ -----------------------------------

module-treemath:
	@echo "==> module-treemath"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::binary_tree::array_representation::treemath' \
		--opaque 'openmls::_' --include 'openmls::binary_tree::array_representation::treemath' \
		$(MODULE_EXCLUDES) --dest-file module-treemath.llbc 2>&1 | tee module-treemath_charon.log

module-binary-tree-tree:
	@echo "==> module-binary-tree-tree"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::binary_tree::array_representation::tree' \
		--opaque 'openmls::_' --include 'openmls::binary_tree::array_representation::tree' \
		$(MODULE_EXCLUDES) --dest-file module-binary-tree-tree.llbc 2>&1 | tee module-binary-tree-tree_charon.log

module-binary-tree-diff:
	@echo "==> module-binary-tree-diff"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::binary_tree::array_representation::diff' \
		--opaque 'openmls::_' --include 'openmls::binary_tree::array_representation::diff' \
		$(MODULE_EXCLUDES) --dest-file module-binary-tree-diff.llbc 2>&1 | tee module-binary-tree-diff_charon.log

module-sorted-iter:
	@echo "==> module-sorted-iter"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::binary_tree::array_representation::sorted_iter' \
		--opaque 'openmls::_' --include 'openmls::binary_tree::array_representation::sorted_iter' \
		$(MODULE_EXCLUDES) --dest-file module-sorted-iter.llbc 2>&1 | tee module-sorted-iter_charon.log

# ----- ciphersuite/ ---------------------------------------------------------

module-aead:
	@echo "==> module-aead"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::aead' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::aead' \
		$(MODULE_EXCLUDES) --dest-file module-aead.llbc 2>&1 | tee module-aead_charon.log

module-hash-ref:
	@echo "==> module-hash-ref"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::hash_ref' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::hash_ref' \
		$(MODULE_EXCLUDES) --dest-file module-hash-ref.llbc 2>&1 | tee module-hash-ref_charon.log

module-hpke:
	@echo "==> module-hpke"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::hpke' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::hpke' \
		$(MODULE_EXCLUDES) --dest-file module-hpke.llbc 2>&1 | tee module-hpke_charon.log

module-kdf-label:
	@echo "==> module-kdf-label"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::kdf_label' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::kdf_label' \
		$(MODULE_EXCLUDES) --dest-file module-kdf-label.llbc 2>&1 | tee module-kdf-label_charon.log

module-mac:
	@echo "==> module-mac"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::mac' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::mac' \
		$(MODULE_EXCLUDES) --dest-file module-mac.llbc 2>&1 | tee module-mac_charon.log

module-reuse-guard:
	@echo "==> module-reuse-guard"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::reuse_guard' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::reuse_guard' \
		$(MODULE_EXCLUDES) --dest-file module-reuse-guard.llbc 2>&1 | tee module-reuse-guard_charon.log

module-secret:
	@echo "==> module-secret"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::secret' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::secret' \
		$(MODULE_EXCLUDES) --dest-file module-secret.llbc 2>&1 | tee module-secret_charon.log

module-signable:
	@echo "==> module-signable"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::signable' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::signable' \
		$(MODULE_EXCLUDES) --dest-file module-signable.llbc 2>&1 | tee module-signable_charon.log

module-signature:
	@echo "==> module-signature"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::ciphersuite::signature' \
		--opaque 'openmls::_' --include 'openmls::ciphersuite::signature' \
		$(MODULE_EXCLUDES) --dest-file module-signature.llbc 2>&1 | tee module-signature_charon.log

# ----- credentials/ ---------------------------------------------------------

module-credentials:
	@echo "==> module-credentials"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::credentials' \
		--opaque 'openmls::_' --include 'openmls::credentials' \
		$(MODULE_EXCLUDES) --dest-file module-credentials.llbc 2>&1 | tee module-credentials_charon.log

# ----- extensions/ ----------------------------------------------------------

module-app-data-dict-extension:
	@echo "==> module-app-data-dict-extension"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::extensions::app_data_dict_extension' \
		--opaque 'openmls::_' --include 'openmls::extensions::app_data_dict_extension' \
		$(MODULE_EXCLUDES) --dest-file module-app-data-dict-extension.llbc 2>&1 | tee module-app-data-dict-extension_charon.log

module-application-id-extension:
	@echo "==> module-application-id-extension"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::extensions::application_id_extension' \
		--opaque 'openmls::_' --include 'openmls::extensions::application_id_extension' \
		$(MODULE_EXCLUDES) --dest-file module-application-id-extension.llbc 2>&1 | tee module-application-id-extension_charon.log

module-external-pub-extension:
	@echo "==> module-external-pub-extension"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::extensions::external_pub_extension' \
		--opaque 'openmls::_' --include 'openmls::extensions::external_pub_extension' \
		$(MODULE_EXCLUDES) --dest-file module-external-pub-extension.llbc 2>&1 | tee module-external-pub-extension_charon.log

module-external-sender-extension:
	@echo "==> module-external-sender-extension"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::extensions::external_sender_extension' \
		--opaque 'openmls::_' --include 'openmls::extensions::external_sender_extension' \
		$(MODULE_EXCLUDES) --dest-file module-external-sender-extension.llbc 2>&1 | tee module-external-sender-extension_charon.log

module-last-resort:
	@echo "==> module-last-resort"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::extensions::last_resort' \
		--opaque 'openmls::_' --include 'openmls::extensions::last_resort' \
		$(MODULE_EXCLUDES) --dest-file module-last-resort.llbc 2>&1 | tee module-last-resort_charon.log

module-ratchet-tree-extension:
	@echo "==> module-ratchet-tree-extension"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::extensions::ratchet_tree_extension' \
		--opaque 'openmls::_' --include 'openmls::extensions::ratchet_tree_extension' \
		$(MODULE_EXCLUDES) --dest-file module-ratchet-tree-extension.llbc 2>&1 | tee module-ratchet-tree-extension_charon.log

module-required-capabilities:
	@echo "==> module-required-capabilities"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::extensions::required_capabilities' \
		--opaque 'openmls::_' --include 'openmls::extensions::required_capabilities' \
		$(MODULE_EXCLUDES) --dest-file module-required-capabilities.llbc 2>&1 | tee module-required-capabilities_charon.log

# ----- framing/ -------------------------------------------------------------

module-message-in:
	@echo "==> module-message-in"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::message_in' \
		--opaque 'openmls::_' --include 'openmls::framing::message_in' \
		$(MODULE_EXCLUDES) --dest-file module-message-in.llbc 2>&1 | tee module-message-in_charon.log

module-message-out:
	@echo "==> module-message-out"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::message_out' \
		--opaque 'openmls::_' --include 'openmls::framing::message_out' \
		$(MODULE_EXCLUDES) --dest-file module-message-out.llbc 2>&1 | tee module-message-out_charon.log

module-mls-auth-content-in:
	@echo "==> module-mls-auth-content-in"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::mls_auth_content_in' \
		--opaque 'openmls::_' --include 'openmls::framing::mls_auth_content_in' \
		$(MODULE_EXCLUDES) --dest-file module-mls-auth-content-in.llbc 2>&1 | tee module-mls-auth-content-in_charon.log

module-mls-auth-content:
	@echo "==> module-mls-auth-content"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::mls_auth_content' \
		--opaque 'openmls::_' --include 'openmls::framing::mls_auth_content' \
		$(MODULE_EXCLUDES) --dest-file module-mls-auth-content.llbc 2>&1 | tee module-mls-auth-content_charon.log

module-mls-content-in:
	@echo "==> module-mls-content-in"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::mls_content_in' \
		--opaque 'openmls::_' --include 'openmls::framing::mls_content_in' \
		$(MODULE_EXCLUDES) --dest-file module-mls-content-in.llbc 2>&1 | tee module-mls-content-in_charon.log

module-mls-content:
	@echo "==> module-mls-content"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::mls_content' \
		--opaque 'openmls::_' --include 'openmls::framing::mls_content' \
		$(MODULE_EXCLUDES) --dest-file module-mls-content.llbc 2>&1 | tee module-mls-content_charon.log

module-private-message-in:
	@echo "==> module-private-message-in"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::private_message_in' \
		--opaque 'openmls::_' --include 'openmls::framing::private_message_in' \
		$(MODULE_EXCLUDES) --dest-file module-private-message-in.llbc 2>&1 | tee module-private-message-in_charon.log

module-private-message:
	@echo "==> module-private-message"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::private_message' \
		--opaque 'openmls::_' --include 'openmls::framing::private_message' \
		$(MODULE_EXCLUDES) --dest-file module-private-message.llbc 2>&1 | tee module-private-message_charon.log

module-public-message-in:
	@echo "==> module-public-message-in"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::public_message_in' \
		--opaque 'openmls::_' --include 'openmls::framing::public_message_in' \
		$(MODULE_EXCLUDES) --dest-file module-public-message-in.llbc 2>&1 | tee module-public-message-in_charon.log

module-public-message:
	@echo "==> module-public-message"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::public_message' \
		--opaque 'openmls::_' --include 'openmls::framing::public_message' \
		$(MODULE_EXCLUDES) --dest-file module-public-message.llbc 2>&1 | tee module-public-message_charon.log

module-sender:
	@echo "==> module-sender"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::sender' \
		--opaque 'openmls::_' --include 'openmls::framing::sender' \
		$(MODULE_EXCLUDES) --dest-file module-sender.llbc 2>&1 | tee module-sender_charon.log

module-framing-validation:
	@echo "==> module-framing-validation"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::framing::validation' \
		--opaque 'openmls::_' --include 'openmls::framing::validation' \
		$(MODULE_EXCLUDES) --dest-file module-framing-validation.llbc 2>&1 | tee module-framing-validation_charon.log

# ----- group/ + group/fork_resolution/ -------------------------------------

module-group-context:
	@echo "==> module-group-context"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::group_context' \
		--opaque 'openmls::_' --include 'openmls::group::group_context' \
		$(MODULE_EXCLUDES) --dest-file module-group-context.llbc 2>&1 | tee module-group-context_charon.log

module-fork-resolution-readd:
	@echo "==> module-fork-resolution-readd"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::fork_resolution::readd' \
		--opaque 'openmls::_' --include 'openmls::group::fork_resolution::readd' \
		$(MODULE_EXCLUDES) --dest-file module-fork-resolution-readd.llbc 2>&1 | tee module-fork-resolution-readd_charon.log

module-fork-resolution-reboot:
	@echo "==> module-fork-resolution-reboot"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::fork_resolution::reboot' \
		--opaque 'openmls::_' --include 'openmls::group::fork_resolution::reboot' \
		$(MODULE_EXCLUDES) --dest-file module-fork-resolution-reboot.llbc 2>&1 | tee module-fork-resolution-reboot_charon.log

# ----- group/mls_group/ -----------------------------------------------------

module-mls-group-app-ephemeral:
	@echo "==> module-mls-group-app-ephemeral"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::app_ephemeral' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::app_ephemeral' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-app-ephemeral.llbc 2>&1 | tee module-mls-group-app-ephemeral_charon.log

module-mls-group-application:
	@echo "==> module-mls-group-application"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::application' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::application' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-application.llbc 2>&1 | tee module-mls-group-application_charon.log

module-mls-group-builder:
	@echo "==> module-mls-group-builder"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::builder' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::builder' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-builder.llbc 2>&1 | tee module-mls-group-builder_charon.log

module-mls-group-commit-builder:
	@echo "==> module-mls-group-commit-builder"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::commit_builder' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::commit_builder' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-commit-builder.llbc 2>&1 | tee module-mls-group-commit-builder_charon.log

module-mls-group-external-commits:
	@echo "==> module-mls-group-external-commits"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::commit_builder::external_commits' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::commit_builder::external_commits' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-external-commits.llbc 2>&1 | tee module-mls-group-external-commits_charon.log

module-mls-group-config:
	@echo "==> module-mls-group-config"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::config' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::config' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-config.llbc 2>&1 | tee module-mls-group-config_charon.log

module-mls-group-creation:
	@echo "==> module-mls-group-creation"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::creation' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::creation' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-creation.llbc 2>&1 | tee module-mls-group-creation_charon.log

module-mls-group-exporting:
	@echo "==> module-mls-group-exporting"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::exporting' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::exporting' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-exporting.llbc 2>&1 | tee module-mls-group-exporting_charon.log

module-mls-group-membership:
	@echo "==> module-mls-group-membership"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::membership' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::membership' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-membership.llbc 2>&1 | tee module-mls-group-membership_charon.log

module-mls-group-past-secrets:
	@echo "==> module-mls-group-past-secrets"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::past_secrets' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::past_secrets' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-past-secrets.llbc 2>&1 | tee module-mls-group-past-secrets_charon.log

module-mls-group-processing:
	@echo "==> module-mls-group-processing"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::processing' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::processing' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-processing.llbc 2>&1 | tee module-mls-group-processing_charon.log

module-mls-group-proposal:
	@echo "==> module-mls-group-proposal"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::proposal' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::proposal' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-proposal.llbc 2>&1 | tee module-mls-group-proposal_charon.log

module-mls-group-proposal-store:
	@echo "==> module-mls-group-proposal-store"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::proposal_store' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::proposal_store' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-proposal-store.llbc 2>&1 | tee module-mls-group-proposal-store_charon.log

module-mls-group-staged-commit:
	@echo "==> module-mls-group-staged-commit"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::staged_commit' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::staged_commit' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-staged-commit.llbc 2>&1 | tee module-mls-group-staged-commit_charon.log

module-mls-group-updates:
	@echo "==> module-mls-group-updates"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::mls_group::updates' \
		--opaque 'openmls::_' --include 'openmls::group::mls_group::updates' \
		$(MODULE_EXCLUDES) --dest-file module-mls-group-updates.llbc 2>&1 | tee module-mls-group-updates_charon.log

# ----- group/public_group/ --------------------------------------------------

module-public-group-builder:
	@echo "==> module-public-group-builder"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::builder' \
		--opaque 'openmls::_' --include 'openmls::group::public_group::builder' \
		$(MODULE_EXCLUDES) --dest-file module-public-group-builder.llbc 2>&1 | tee module-public-group-builder_charon.log

module-public-group-diff:
	@echo "==> module-public-group-diff"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::diff' \
		--opaque 'openmls::_' --include 'openmls::group::public_group::diff' \
		$(MODULE_EXCLUDES) --dest-file module-public-group-diff.llbc 2>&1 | tee module-public-group-diff_charon.log

module-public-group-apply-proposals:
	@echo "==> module-public-group-apply-proposals"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::diff::apply_proposals' \
		--opaque 'openmls::_' --include 'openmls::group::public_group::diff::apply_proposals' \
		$(MODULE_EXCLUDES) --dest-file module-public-group-apply-proposals.llbc 2>&1 | tee module-public-group-apply-proposals_charon.log

module-public-group-compute-path:
	@echo "==> module-public-group-compute-path"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::diff::compute_path' \
		--opaque 'openmls::_' --include 'openmls::group::public_group::diff::compute_path' \
		$(MODULE_EXCLUDES) --dest-file module-public-group-compute-path.llbc 2>&1 | tee module-public-group-compute-path_charon.log

module-public-group-process:
	@echo "==> module-public-group-process"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::process' \
		--opaque 'openmls::_' --include 'openmls::group::public_group::process' \
		$(MODULE_EXCLUDES) --dest-file module-public-group-process.llbc 2>&1 | tee module-public-group-process_charon.log

module-public-group-staged-commit:
	@echo "==> module-public-group-staged-commit"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::staged_commit' \
		--opaque 'openmls::_' --include 'openmls::group::public_group::staged_commit' \
		$(MODULE_EXCLUDES) --dest-file module-public-group-staged-commit.llbc 2>&1 | tee module-public-group-staged-commit_charon.log

module-public-group-validation:
	@echo "==> module-public-group-validation"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::group::public_group::validation' \
		--opaque 'openmls::_' --include 'openmls::group::public_group::validation' \
		$(MODULE_EXCLUDES) --dest-file module-public-group-validation.llbc 2>&1 | tee module-public-group-validation_charon.log

# ----- key_packages/ --------------------------------------------------------

module-key-packages:
	@echo "==> module-key-packages"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::key_packages' \
		--opaque 'openmls::_' --include 'openmls::key_packages' \
		$(MODULE_EXCLUDES) --dest-file module-key-packages.llbc 2>&1 | tee module-key-packages_charon.log

module-key-package-in:
	@echo "==> module-key-package-in"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::key_packages::key_package_in' \
		--opaque 'openmls::_' --include 'openmls::key_packages::key_package_in' \
		$(MODULE_EXCLUDES) --dest-file module-key-package-in.llbc 2>&1 | tee module-key-package-in_charon.log

module-lifetime:
	@echo "==> module-lifetime"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::key_packages::lifetime' \
		--opaque 'openmls::_' --include 'openmls::key_packages::lifetime' \
		$(MODULE_EXCLUDES) --dest-file module-lifetime.llbc 2>&1 | tee module-lifetime_charon.log

# ----- messages/ ------------------------------------------------------------

module-external-proposals:
	@echo "==> module-external-proposals"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::messages::external_proposals' \
		--opaque 'openmls::_' --include 'openmls::messages::external_proposals' \
		$(MODULE_EXCLUDES) --dest-file module-external-proposals.llbc 2>&1 | tee module-external-proposals_charon.log

module-group-info:
	@echo "==> module-group-info"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::messages::group_info' \
		--opaque 'openmls::_' --include 'openmls::messages::group_info' \
		$(MODULE_EXCLUDES) --dest-file module-group-info.llbc 2>&1 | tee module-group-info_charon.log

module-proposals:
	@echo "==> module-proposals"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::messages::proposals' \
		--opaque 'openmls::_' --include 'openmls::messages::proposals' \
		$(MODULE_EXCLUDES) --dest-file module-proposals.llbc 2>&1 | tee module-proposals_charon.log

module-proposals-in:
	@echo "==> module-proposals-in"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::messages::proposals_in' \
		--opaque 'openmls::_' --include 'openmls::messages::proposals_in' \
		$(MODULE_EXCLUDES) --dest-file module-proposals-in.llbc 2>&1 | tee module-proposals-in_charon.log

module-app-data-update:
	@echo "==> module-app-data-update"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::messages::proposals::app_data_update' \
		--opaque 'openmls::_' --include 'openmls::messages::proposals::app_data_update' \
		$(MODULE_EXCLUDES) --dest-file module-app-data-update.llbc 2>&1 | tee module-app-data-update_charon.log

# ----- schedule/ ------------------------------------------------------------

module-application-export-tree:
	@echo "==> module-application-export-tree"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::schedule::application_export_tree' \
		--opaque 'openmls::_' --include 'openmls::schedule::application_export_tree' \
		$(MODULE_EXCLUDES) --dest-file module-application-export-tree.llbc 2>&1 | tee module-application-export-tree_charon.log

module-message-secrets:
	@echo "==> module-message-secrets"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::schedule::message_secrets' \
		--opaque 'openmls::_' --include 'openmls::schedule::message_secrets' \
		$(MODULE_EXCLUDES) --dest-file module-message-secrets.llbc 2>&1 | tee module-message-secrets_charon.log

module-psk:
	@echo "==> module-psk"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::schedule::psk' \
		--opaque 'openmls::_' --include 'openmls::schedule::psk' \
		$(MODULE_EXCLUDES) --dest-file module-psk.llbc 2>&1 | tee module-psk_charon.log

module-pprf-input:
	@echo "==> module-pprf-input"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::schedule::pprf::input' \
		--opaque 'openmls::_' --include 'openmls::schedule::pprf::input' \
		$(MODULE_EXCLUDES) --dest-file module-pprf-input.llbc 2>&1 | tee module-pprf-input_charon.log

module-pprf-prefix:
	@echo "==> module-pprf-prefix"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::schedule::pprf::prefix' \
		--opaque 'openmls::_' --include 'openmls::schedule::pprf::prefix' \
		$(MODULE_EXCLUDES) --dest-file module-pprf-prefix.llbc 2>&1 | tee module-pprf-prefix_charon.log

# ----- tree/ ----------------------------------------------------------------

module-secret-tree:
	@echo "==> module-secret-tree"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::tree::secret_tree' \
		--opaque 'openmls::_' --include 'openmls::tree::secret_tree' \
		$(MODULE_EXCLUDES) --dest-file module-secret-tree.llbc 2>&1 | tee module-secret-tree_charon.log

module-sender-ratchet:
	@echo "==> module-sender-ratchet"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::tree::sender_ratchet' \
		--opaque 'openmls::_' --include 'openmls::tree::sender_ratchet' \
		$(MODULE_EXCLUDES) --dest-file module-sender-ratchet.llbc 2>&1 | tee module-sender-ratchet_charon.log

# ----- treesync/ ------------------------------------------------------------

module-treesync-diff:
	@echo "==> module-treesync-diff"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::diff' \
		--opaque 'openmls::_' --include 'openmls::treesync::diff' \
		$(MODULE_EXCLUDES) --dest-file module-treesync-diff.llbc 2>&1 | tee module-treesync-diff_charon.log

module-treesync-hashes:
	@echo "==> module-treesync-hashes"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::hashes' \
		--opaque 'openmls::_' --include 'openmls::treesync::hashes' \
		$(MODULE_EXCLUDES) --dest-file module-treesync-hashes.llbc 2>&1 | tee module-treesync-hashes_charon.log

module-treesync-node:
	@echo "==> module-treesync-node"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::node' \
		--opaque 'openmls::_' --include 'openmls::treesync::node' \
		$(MODULE_EXCLUDES) --dest-file module-treesync-node.llbc 2>&1 | tee module-treesync-node_charon.log

module-treekem:
	@echo "==> module-treekem"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::treekem' \
		--opaque 'openmls::_' --include 'openmls::treesync::treekem' \
		$(MODULE_EXCLUDES) --dest-file module-treekem.llbc 2>&1 | tee module-treekem_charon.log

module-treesync-node-internal:
	@echo "==> module-treesync-node-internal"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::treesync_node' \
		--opaque 'openmls::_' --include 'openmls::treesync::treesync_node' \
		$(MODULE_EXCLUDES) --dest-file module-treesync-node-internal.llbc 2>&1 | tee module-treesync-node-internal_charon.log

# ----- treesync/node/ -------------------------------------------------------

module-encryption-keys:
	@echo "==> module-encryption-keys"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::node::encryption_keys' \
		--opaque 'openmls::_' --include 'openmls::treesync::node::encryption_keys' \
		$(MODULE_EXCLUDES) --dest-file module-encryption-keys.llbc 2>&1 | tee module-encryption-keys_charon.log

module-leaf-node:
	@echo "==> module-leaf-node"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::node::leaf_node' \
		--opaque 'openmls::_' --include 'openmls::treesync::node::leaf_node' \
		$(MODULE_EXCLUDES) --dest-file module-leaf-node.llbc 2>&1 | tee module-leaf-node_charon.log

module-leaf-node-capabilities:
	@echo "==> module-leaf-node-capabilities"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::node::leaf_node::capabilities' \
		--opaque 'openmls::_' --include 'openmls::treesync::node::leaf_node::capabilities' \
		$(MODULE_EXCLUDES) --dest-file module-leaf-node-capabilities.llbc 2>&1 | tee module-leaf-node-capabilities_charon.log

module-parent-node:
	@echo "==> module-parent-node"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::treesync::node::parent_node' \
		--opaque 'openmls::_' --include 'openmls::treesync::node::parent_node' \
		$(MODULE_EXCLUDES) --dest-file module-parent-node.llbc 2>&1 | tee module-parent-node_charon.log

# ----- top-level files ------------------------------------------------------

module-grease:
	@echo "==> module-grease"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::grease' \
		--opaque 'openmls::_' --include 'openmls::grease' \
		$(MODULE_EXCLUDES) --dest-file module-grease.llbc 2>&1 | tee module-grease_charon.log

module-skip-validation:
	@echo "==> module-skip-validation"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::skip_validation' \
		--opaque 'openmls::_' --include 'openmls::skip_validation' \
		$(MODULE_EXCLUDES) --dest-file module-skip-validation.llbc 2>&1 | tee module-skip-validation_charon.log

module-storage:
	@echo "==> module-storage"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::storage' \
		--opaque 'openmls::_' --include 'openmls::storage' \
		$(MODULE_EXCLUDES) --dest-file module-storage.llbc 2>&1 | tee module-storage_charon.log

module-versions:
	@echo "==> module-versions"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		--start-from 'openmls::versions' \
		--opaque 'openmls::_' --include 'openmls::versions' \
		$(MODULE_EXCLUDES) --dest-file module-versions.llbc 2>&1 | tee module-versions_charon.log

# ----- Per-module bulk + status --------------------------------------------

MODULE_TARGETS := \
	module-treemath module-binary-tree-tree module-binary-tree-diff module-sorted-iter \
	module-aead module-hash-ref module-hpke module-kdf-label module-mac \
	module-reuse-guard module-secret module-signable module-signature \
	module-credentials \
	module-app-data-dict-extension module-application-id-extension \
	module-external-pub-extension module-external-sender-extension \
	module-last-resort module-ratchet-tree-extension module-required-capabilities \
	module-message-in module-message-out \
	module-mls-auth-content-in module-mls-auth-content \
	module-mls-content-in module-mls-content \
	module-private-message-in module-private-message \
	module-public-message-in module-public-message \
	module-sender module-framing-validation \
	module-group-context \
	module-fork-resolution-readd module-fork-resolution-reboot \
	module-mls-group-app-ephemeral module-mls-group-application \
	module-mls-group-builder module-mls-group-commit-builder \
	module-mls-group-external-commits module-mls-group-config \
	module-mls-group-creation module-mls-group-exporting \
	module-mls-group-membership module-mls-group-past-secrets \
	module-mls-group-processing module-mls-group-proposal \
	module-mls-group-proposal-store module-mls-group-staged-commit \
	module-mls-group-updates \
	module-public-group-builder module-public-group-diff \
	module-public-group-apply-proposals module-public-group-compute-path \
	module-public-group-process module-public-group-staged-commit \
	module-public-group-validation \
	module-key-packages module-key-package-in module-lifetime \
	module-external-proposals module-group-info module-proposals \
	module-proposals-in module-app-data-update \
	module-application-export-tree module-message-secrets module-psk \
	module-pprf-input module-pprf-prefix \
	module-secret-tree module-sender-ratchet \
	module-treesync-diff module-treesync-hashes module-treesync-node \
	module-treekem module-treesync-node-internal \
	module-encryption-keys module-leaf-node module-leaf-node-capabilities \
	module-parent-node \
	module-grease module-skip-validation module-storage module-versions

# Module paths covered by the per-module sweep (excluding the 8 feature-gated
# failures: extensions-draft-08 × 6, fork-resolution × 2). Used by the
# combined single-LLBC recipe below.
MODULE_PATHS := \
	binary_tree::array_representation::treemath \
	binary_tree::array_representation::tree \
	binary_tree::array_representation::diff \
	binary_tree::array_representation::sorted_iter \
	ciphersuite::aead ciphersuite::hash_ref ciphersuite::hpke \
	ciphersuite::kdf_label ciphersuite::mac ciphersuite::reuse_guard \
	ciphersuite::secret ciphersuite::signable ciphersuite::signature \
	credentials \
	extensions::application_id_extension \
	extensions::external_pub_extension extensions::external_sender_extension \
	extensions::last_resort extensions::ratchet_tree_extension \
	extensions::required_capabilities \
	framing::message_in framing::message_out \
	framing::mls_auth_content_in framing::mls_auth_content \
	framing::mls_content_in framing::mls_content \
	framing::private_message_in framing::private_message \
	framing::public_message_in framing::public_message \
	framing::sender framing::validation \
	group::group_context \
	group::mls_group::application group::mls_group::builder \
	group::mls_group::commit_builder \
	group::mls_group::commit_builder::external_commits \
	group::mls_group::config group::mls_group::creation \
	group::mls_group::exporting group::mls_group::membership \
	group::mls_group::past_secrets group::mls_group::processing \
	group::mls_group::proposal group::mls_group::proposal_store \
	group::mls_group::staged_commit group::mls_group::updates \
	group::public_group::builder group::public_group::diff \
	group::public_group::diff::apply_proposals \
	group::public_group::diff::compute_path \
	group::public_group::process group::public_group::staged_commit \
	group::public_group::validation \
	key_packages key_packages::key_package_in key_packages::lifetime \
	messages::external_proposals messages::group_info \
	messages::proposals messages::proposals_in \
	schedule::message_secrets schedule::psk \
	tree::secret_tree tree::sender_ratchet \
	treesync::diff treesync::hashes treesync::node \
	treesync::treekem treesync::treesync_node \
	treesync::node::encryption_keys treesync::node::leaf_node \
	treesync::node::leaf_node::capabilities treesync::node::parent_node \
	grease skip_validation storage versions

# Full-crate single LLBC with only the four standard trait-impl excludes
# (Serialize, Deserialize, Debug, Display) — no opacity confinement, no
# per-module include list. Every openmls item that compiles under default
# cargo features is translated fully (test code auto-excluded by
# cfg(test)=false). Should produce zero opaque-enum-discriminant warnings
# because every enum in the crate is now transparent.
module-fullcrate-charon:
	@echo "==> module-fullcrate-charon (full crate, default features, standard excludes)"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		$(MODULE_EXCLUDES) \
		--dest-file module-fullcrate.llbc 2>&1 | tee module-fullcrate_charon.log

# Single LLBC over all 78 working modules, with the same opacity-confinement
# pattern as the per-module recipes — every openmls item outside the covered
# set is signature-only. Useful as a "what the sweep collectively translates"
# artefact, and as input to downstream pipelines that prefer one file.
module-combined-charon:
	@echo "==> module-combined-charon ($(words $(MODULE_PATHS)) modules)"
	@cd $(CRATE_DIR) && charon cargo --preset aeneas \
		$(foreach p,$(MODULE_PATHS),--start-from 'openmls::$(p)') \
		--opaque 'openmls::_' \
		$(foreach p,$(MODULE_PATHS),--include 'openmls::$(p)') \
		$(MODULE_EXCLUDES) \
		--dest-file module-combined.llbc 2>&1 | tee module-combined_charon.log

# Run all per-module recipes. `-k` keeps going past individual failures so we
# get a full sweep rather than aborting at the first error.
module-all-charon:
	@$(MAKE) -k $(MODULE_TARGETS) || true
	@echo "==> module-all-charon complete; see module-*_charon.log for details"

# Tabulate a one-line status per recipe into module_status.md (workspace root,
# next to the LLBCs). Counts charon-driver "error:" lines and the four known
# Box-init / region warnings.
# Script lives at openmls_proofwork/scripts/, but the Makefile dir itself
# is a symlink target so $(CURDIR) resolves into /home/.../openmls — go
# back through the workspace tree to find scripts/.
MODULE_STATUS_SCRIPT := $(CURDIR)/../openmls_proofwork/scripts/module_status.py

module-status-charon:
	@cd $(CRATE_DIR) && python3 $(MODULE_STATUS_SCRIPT) > $(CURDIR)/module_status.md && echo "wrote $(CURDIR)/module_status.md"

help:
	@echo "Per-target FV extraction recipes — one triple per target:"
	@echo "  extract-<short>   charon  → LLBC          (artifact: <short>.llbc, log: <short>_charon.log)"
	@echo "  hax-<short>       hax     → Lean (direct) (log: <short>_hax.log)"
	@echo "  aeneas-<short>    hax     → aeneas → Lean (log: <short>_aeneas.log)"
	@echo ""
	@echo "  <short> ∈ { treemath  parenthash  valid     welcome  skipval"
	@echo "              extcommit tbs         mutatomic zeroize  reinit"
	@echo "              sigkey    kpsig       respsk }"
	@echo ""
	@echo "Bulk:"
	@echo "  extract-all-fv    charon on all 13 FV targets"
	@echo "  hax-all-fv        hax-direct on all 13 FV targets"
	@echo "  aeneas-all-fv     hax-aeneas on all 13 FV targets"
	@echo ""
	@echo "Umbrella (full INCLUDE filter):"
	@echo "  extract           hax → Lean (output: $(HAX_OUTPUT))"
	@echo "  extract-charon    charon → LLBC (artifact: $(LLBC_OUTPUT), log: $(CHARON_OUTPUT))"
	@echo ""
	@echo "Per-module charon sweep (opacity-confined; one LLBC per substantive .rs):"
	@echo "  module-<short>     run charon on a single module"
	@echo "  module-all-charon  run all $(words $(MODULE_TARGETS)) module recipes (use -k to keep going on failures)"
	@echo "  module-status-charon  tabulate results into module_status.md"
