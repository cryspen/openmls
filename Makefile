# OpenMLS — hax-lean extraction
#
# Workflow: `make extract` runs hax once with the cumulative INCLUDE
# filter below. Each `+` line is a target module from `../extraction.org`;
# add `-…` lines after a `+` to carve out FV-irrelevant items inside that
# module. Per-module rationale lives in `../extraction.org`.
#
# Run from the workspace root (this directory).

# Use bash with pipefail so `make` notices hax failures even though we tee
# through a pipe (sh's default would mask them).
SHELL := /bin/bash
.SHELLFLAGS := -o pipefail -c

CRATE_DIR  := openmls
HAX_OUTPUT := /tmp/hax_output

# ----- Currently active extraction filter -----------------------------------
INCLUDE := -**

# --- Toolchain pilots (already extracted) ---
INCLUDE += +openmls::ciphersuite::aead::**
INCLUDE += +openmls::ciphersuite::secret::**

# --- The ten FV targets (priority order matches extraction.org) ---
# 1. skip_validation                       (FV #5, smallest pilot)
INCLUDE += +openmls::skip_validation::**
# 2. public_group::validation              (FV #1, #6 — central validator)
INCLUDE += +openmls::group::public_group::validation::**
# 3. public_group::staged_commit           (FV #6 — external-commit allowlist)
INCLUDE += +openmls::group::public_group::staged_commit::**
# 4. mls_group::commit_builder::external_commits  (FV #6 — sender side, H-4)
# Commented out: 4 errors (HAX0003/HAX0010) at L300-302. See extraction.org.
# INCLUDE += +openmls::group::mls_group::commit_builder::external_commits::**
# 5. key_packages::key_package_in          (FV #1 — standalone validation)
INCLUDE += +openmls::key_packages::key_package_in::**
# 6. key_packages::lifetime                (FV #1 — M-5 dead defensive code)
INCLUDE += +openmls::key_packages::lifetime::**
# 7. treesync::node::leaf_node             (FV #1, #7 — validate_locally + TBS)
INCLUDE += +openmls::treesync::node::leaf_node::**
# 8. mls_group::creation                   (FV #2 — Welcome typestate)
INCLUDE += +openmls::group::mls_group::creation::**
# 9. treesync::diff                        (FV #3, #8 — parent-hash + atomicity)
# Commented out: 39 errors (29× HAX0002 "type Dyn with non trait predicate"
# plus HAX0003/0010/0008 cluster). See extraction.org.
# INCLUDE += +openmls::treesync::diff::**
# 10. treesync::node::parent_node          (FV #3 — UnmergedLeaves M-2)
INCLUDE += +openmls::treesync::node::parent_node::**

# ----- Recipe ---------------------------------------------------------------
.PHONY: extract help

extract:
	@echo "==> extract (output: $(HAX_OUTPUT))"
	@cd $(CRATE_DIR) && cargo hax into -i '$(strip $(INCLUDE))' lean 2>&1 | tee $(HAX_OUTPUT)

help:
	@echo "Edit INCLUDE in this Makefile, then run: make extract"
