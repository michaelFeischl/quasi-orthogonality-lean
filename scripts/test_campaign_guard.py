#!/usr/bin/env python3
"""Mutation tests use small temporary project copies; dependencies stay read-only."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('campaign_guard', HERE / 'scripts/check_campaign.py')
assert spec and spec.loader
GUARD = importlib.util.module_from_spec(spec)
spec.loader.exec_module(GUARD)


class GuardMutations(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='campaign-guard-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in ('Autoformalization', 'sources'):
            shutil.copytree(HERE / name, self.root / name)
        for name in ('Autoformalization.lean', *GUARD.PIN_HASHES):
            shutil.copy2(HERE / name, self.root / name)
        (self.root / 'docs').mkdir()
        shutil.copy2(HERE / 'docs/frozen-anchor-manifest.json', self.root / 'docs/frozen-anchor-manifest.json')
        # No dependency tree is copied or modified by these mutation tests.
        (self.root / '.lake').mkdir()
        (self.root / '.lake/packages').symlink_to(HERE / '.lake/packages', target_is_directory=True)
        self.manifest = json.loads((self.root / 'docs/frozen-anchor-manifest.json').read_text())

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def errors(self):
        guard = GUARD.CampaignGuard(self.root)
        try:
            guard.campaign(self.manifest, dependencies=False)
        except (ValueError, KeyError, TypeError) as error:
            guard.fail(f'cannot validate campaign: {error}')
        return '\n'.join(guard.errors)

    def catches(self, expected):
        self.assertIn(expected, self.errors())

    def draft_provider(self, anchor_id='pg_qo_v1'):
        """Create a draft fixture independently of live campaign proof status."""
        anchor = next(a for a in self.manifest['anchors'] if a['id'] == anchor_id)
        anchor['state'] = 'DRAFT_SORRY'
        path = self.root / anchor['path']
        prefix, rest = path.read_text().split('-- FROZEN_ANCHOR_PROOF_BEGIN\n', 1)
        _, suffix = rest.split('-- FROZEN_ANCHOR_PROOF_END', 1)
        path.write_text(prefix + '-- FROZEN_ANCHOR_PROOF_BEGIN\nby sorry\n' +
                        '-- FROZEN_ANCHOR_PROOF_END' + suffix)
        self.write('Autoformalization.lean', 'module\npublic import Autoformalization.PetrovGalerkin.ScalarReduction\n')
        self.assertEqual('', self.errors())
        return anchor['implementation']['module']

    def test_clean_baseline(self):
        self.assertEqual('', self.errors())

    def test_inline_elaborator(self):
        self.write('Autoformalization/Evil.lean', 'module\nopen Lean Meta Elab Term in elab "fake" : term => pure default\n')
        self.catches("forbidden construct 'elab'")

    def test_metaprogramming_variants(self):
        for token in ('elab_rules', 'macro', 'macro_rules', 'syntax', 'run_cmd', 'run_elab', 'run_meta', 'run_tac', 'by_elab', 'addDecl', 'set_option debug.skipKernelTC'):
            with self.subTest(token=token):
                self.write('Autoformalization/Evil.lean', 'module\nopen Lean in ' + token + '\n')
                self.catches('forbidden construct')

    def test_registration_attributes(self):
        for attr in ('command_elab', 'term_elab', 'tactic', 'macro'):
            for form in ('@[\n%s foo]\ndef x := 1', 'attribute [local %s foo] x'):
                with self.subTest(attr=attr, form=form):
                    self.write('Autoformalization/Evil.lean', 'module\n' + form % attr)
                    self.catches('forbidden construct')

    def test_hidden_provider_consumer(self):
        provider = self.draft_provider()
        self.write('Bridge.lean', 'module\npublic import ' + provider + '\n')
        self.write('Autoformalization/Consumer.lean', 'module\npublic import Bridge\n')
        errors = self.errors()
        self.assertIn('DRAFT provider imported directly or transitively', errors)
        self.assertIn('Consumer.lean', errors)

    def test_multiple_imports_cannot_hide_provider(self):
        provider = self.draft_provider()
        self.write('Autoformalization/Consumer.lean', 'module\nimport Mathlib ' + provider + '\n')
        self.catches('DRAFT provider imported directly or transitively')

    def test_frozen_bytes(self):
        path = self.root / self.manifest['anchors'][0]['path']
        path.write_bytes(path.read_bytes().replace(b'module\n', b'module  \n', 1))
        self.catches('frozen prefix hash drift')

    def test_unauthorized_sorry(self):
        self.write('.scratch/Probe.lean', 'module\nexample : True := by sorry\n')
        self.catches('unauthorized `sorry`')

    def test_custom_axiom_inline(self):
        self.write('Autoformalization/Evil.lean', 'module\nnamespace Sneaky in axiom falsehood : False\n')
        self.catches("forbidden construct 'axiom'")

    def test_normal_scratch_probe_allowed(self):
        self.write('.scratch/Probe.lean', 'module\nimport Autoformalization.PetrovGalerkin.ScalarReduction\n#print axioms Autoformalization.PetrovGalerkin.reduction_coefficient_pos\nexample : True := by trivial\n')
        self.assertEqual('', self.errors())

    def test_scratch_provider_consumer_rejected(self):
        self.write('.scratch/Probe.lean', 'module\nimport ' + self.draft_provider() + '\n')
        self.catches('DRAFT provider imported directly or transitively')

    def test_untracked_module_header_required(self):
        self.write('Autoformalization/New.lean', 'theorem test : True := by trivial\n')
        self.catches('missing module header')

    def test_unapproved_transitive_root(self):
        self.write('Bridge.lean', 'module\npublic import Autoformalization.PetrovGalerkin.ScalarReduction\n')
        self.write('Autoformalization/Middle.lean', 'module\npublic import Bridge\n')
        self.write('Autoformalization.lean', 'module\npublic import Autoformalization.Middle\n')
        self.catches('production imports unapproved project root: Bridge')

    def test_extra_library(self):
        with (self.root / 'lakefile.toml').open('a') as handle:
            handle.write('\n[[lean_lib]]\nname = "Bridge"\n')
        self.catches('unapproved lean_lib configuration')

    def test_unknown_external_import(self):
        self.write('Autoformalization.lean', 'module\npublic import UnpinnedPackage.Evil\n')
        self.catches('import outside pinned external packages')

    def test_source_drift(self):
        pinned_sources = sorted({
            anchor['source']['range'].split(':', 1)[0]
            for anchor in self.manifest['anchors']
        })
        self.assertTrue(pinned_sources)
        for pinned_source in pinned_sources:
            with self.subTest(source=pinned_source):
                path = self.root / pinned_source
                original = path.read_bytes()
                try:
                    path.write_bytes(original + b'\n% changed source\n')
                    self.catches('source revision drift: ' + pinned_source)
                finally:
                    path.write_bytes(original)
                self.assertEqual('', self.errors())

    def test_revision_draft_frozen_imports_rejected(self):
        for anchor_id in ('hs_qo_v1', 'pg_assumptions_v1'):
            with self.subTest(anchor=anchor_id):
                self.draft_provider(anchor_id)
                anchor = next(a for a in self.manifest['anchors'] if a['id'] == anchor_id)
                module = anchor['path'].removesuffix('.lean').replace('/', '.')
                path = self.root / 'Autoformalization/Consumer.lean'
                try:
                    self.write('Autoformalization/Consumer.lean', 'module\nimport ' + module + '\n')
                    self.catches(anchor_id + ': DRAFT_SORRY imported directly or transitively')
                finally:
                    path.unlink()
                self.assertEqual('', self.errors())

    def test_draft_provider_cannot_consume_other_draft_provider(self):
        first = self.draft_provider('hs_qo_v1')
        second = self.draft_provider('pg_assumptions_v1')
        first_path = self.root / (first.replace('.', '/') + '.lean')
        original = first_path.read_bytes()
        try:
            first_path.write_text('module\nimport ' + second + '\n')
            self.catches('pg_assumptions_v1: DRAFT provider imported directly or transitively')
        finally:
            first_path.write_bytes(original)
        self.assertEqual('', self.errors())

    def test_pin_drift(self):
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:nightly\n')
        self.catches('dependency/config pin drift')

    def test_dependency_dirty_source_and_wrong_revision(self):
        # A tiny independent Git fixture exercises read-only dependency checks.
        (self.root / '.lake/packages').unlink()
        package = self.root / '.lake/packages/tiny'
        package.mkdir(parents=True)
        def git(*args):
            return subprocess.run(['git', '-C', str(package), *args], capture_output=True, text=True, check=True).stdout.strip()
        git('init', '-q')
        (package / 'Tiny.lean').write_text('module\n')
        git('add', 'Tiny.lean')
        git('-c', 'user.name=Guard Test', '-c', 'user.email=guard@example.invalid', 'commit', '-qm', 'fixture')
        pin = {'name': 'tiny', 'rev': git('rev-parse', 'HEAD')}
        guard = GUARD.CampaignGuard(self.root)
        guard.check_dependencies([pin])
        self.assertEqual([], guard.errors)
        (package / 'Tiny.lean').write_text('module\n-- source changed\n')
        guard.check_dependencies([pin])
        self.assertIn('dependency source tree dirty: tiny', '\n'.join(guard.errors))
        guard.check_dependencies([{'name': 'tiny', 'rev': '0' * 40}])
        self.assertIn('dependency revision drift: tiny', '\n'.join(guard.errors))

    def test_scratch_header_required(self):
        self.write('.scratch/Probe.lean', 'example : True := by trivial\n')
        self.catches('missing module header')

    def test_comments_strings_are_masked(self):
        self.write('Autoformalization/Comments.lean', 'module\n/- outer /- elab sorry -/ axiom -/\n-- run_cmd\ndef text := "macro axiom sorry"\ndef apostrophe : Char := \'a\'\n')
        self.assertEqual('', self.errors())

    def test_name_quote_does_not_swallow_code(self):
        self.write('Autoformalization/Evil.lean', "module\n#check 'foo\nrun_cmd pure ()\n")
        self.catches("forbidden construct 'run_cmd'")

    def test_duplicate_export_owner(self):
        self.write('Autoformalization/Duplicate.lean', 'module\npublic theorem ' + self.manifest['anchors'][0]['export'] + ' : True := by trivial\n')
        self.catches('frozen export must have one unique owner')

    # Independent adversarial review: executable interpolation must not be
    # treated as inert string text, and inline commands must not evade owners.
    def test_interpolated_string_cannot_hide_sorry(self):
        self.write('Autoformalization/Interpolation.lean',
                   'module\npublic def hidden : String := s!"{(by sorry : Nat)}"\n')
        self.catches('unsupported prefixed string')

    def test_sibling_interpolators_cannot_hide_executable_terms(self):
        for prefix in ('m!', 'f! ', 's! /- separator -/ '):
            with self.subTest(prefix=prefix):
                self.write('Autoformalization/Interpolation.lean',
                           'module\nimport Lean\npublic def hidden := ' + prefix
                           + '"{(by sorry : Nat)}"\n')
                self.catches('unsupported prefixed string')

    def test_contextual_interpolation_cannot_hide_executable_terms(self):
        self.write('Autoformalization/Interpolation.lean',
                   'module\npublic def hidden : Nat := dbg_trace "{(by sorry : Nat)}"; 0\n')
        self.catches("forbidden construct 'dbg_trace'")

    def test_inline_duplicate_owner_in_namespace(self):
        namespace, name = self.manifest['anchors'][0]['export'].rsplit('.', 1)
        self.write('Autoformalization/Duplicate.lean',
                   'module\nnamespace ' + namespace + '\nopen Nat in public theorem ' + name
                   + ' : True := by trivial\nend ' + namespace + '\n')
        self.catches('unsupported scoped declaration formatting')

    def test_quoted_debug_option_cannot_bypass_lint(self):
        self.write('Autoformalization/DebugOption.lean',
                   'module\nset_option «debug».«skipKernelTC» true\n')
        self.catches("forbidden construct 'set_option «debug».'")

    def test_multiline_provider_import_fails_closed(self):
        provider = self.manifest['anchors'][0]['implementation']['module']
        self.write('Autoformalization/Consumer.lean', 'module\npublic import\n  ' + provider + '\n')
        self.catches('unsupported import syntax')

    def test_source_escape_fails_closed(self):
        self.manifest['anchors'][0]['source']['range'] = 'lean-toolchain:1-1'
        self.catches('source path outside sources')


if __name__ == '__main__':
    unittest.main(verbosity=2)
