#!/usr/bin/env python3
"""Regression checks for proof audits, source layout and release metadata."""
import json
import re
import subprocess
import tempfile
import tomllib
import unittest
from pathlib import Path
from unittest.mock import patch
import release
from check_imports import imports
from check_standalone import check_layout
from check_vendor import ROOT, check_package_pins
class Checks(unittest.TestCase):
    def test_public_imports_and_nested_comments(self):
        source = 'module\npublic import Foundation.A\nmeta import Mathlib.B\n/- import Bogus.C /- nested -/ -/\n-- import Bogus.D\nimport ClassicalTheorems.Audit\n'
        self.assertEqual(imports(source), ['Foundation.A', 'Mathlib.B', 'ClassicalTheorems.Audit'])
    def test_standalone_layout_rejects_external_dependency_and_cache_link(self):
        with tempfile.TemporaryDirectory(prefix='classical-layout-') as directory:
            base = Path(directory)
            root = base/'project'
            root.mkdir()
            (root/'lakefile.toml').write_text('name = "fixture"\n')
            (root/'lake-manifest.json').write_text(json.dumps({'packagesDir': '.lake/packages', 'packages': []}))
            check_layout(root)
            (root/'lakefile.toml').write_text('name = "fixture"\n[[require]]\nname = "external"\npath = "../external"\n')
            with self.assertRaises(AssertionError): check_layout(root)
            (root/'lakefile.toml').write_text('name = "fixture"\n')
            external = base/'external'
            external.mkdir()
            (root/'.lake').symlink_to('../external', target_is_directory=True)
            with self.assertRaises(AssertionError): check_layout(root)
    def test_package_pins_reject_toolchain_and_mathlib_drift(self):
        with tempfile.TemporaryDirectory(prefix='classical-pins-') as directory:
            root = Path(directory)
            package = ROOT/'vendor/hol-light-port'
            names = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
            original = {name: (package/name).read_text() for name in names}
            toolchain = (ROOT/'lean-toolchain').read_text().strip()
            config = tomllib.loads((ROOT/'lakefile.toml').read_text())
            revision = next(dep['rev'] for dep in config['require'] if dep['name'] == 'mathlib')
            for case in ['valid', 'toolchain', 'lock', 'shared-revision', 'dependency-kind']:
                for name, text in original.items():
                    (root/name).write_text(text)
                if case == 'toolchain':
                    (root/'lean-toolchain').write_text('leanprover/lean4:v4.0.0\n')
                elif case != 'valid':
                    lock = json.loads(original['lake-manifest.json'])
                    pin = next(p for p in lock['packages'] if p['name'] == 'mathlib')
                    if case == 'dependency-kind':
                        pin['type'] = 'path'
                    else:
                        pin['rev'] = '0' * 40
                    (root/'lake-manifest.json').write_text(json.dumps(lock))
                    if case == 'shared-revision':
                        (root/'lakefile.toml').write_text(original['lakefile.toml'].replace(revision, pin['rev']))
                with self.subTest(case=case):
                    if case == 'valid':
                        check_package_pins(root, toolchain, revision)
                    else:
                        with self.assertRaises(AssertionError):
                            check_package_pins(root, toolchain, revision)

    def test_release_metadata_rejects_mismatches_and_unsafe_values(self):
        with tempfile.TemporaryDirectory(prefix='classical-metadata-') as directory:
            root = Path(directory)
            original = {name: (ROOT/name).read_text()
                        for name in ['CITATION.cff', 'lakefile.toml']}
            current_version = tomllib.loads(original['lakefile.toml'])['version']

            def package_for(version):
                return re.sub(r'^version\s*=.*$', f'version = "{version}"',
                              original['lakefile.toml'], count=1, flags=re.M)

            cases = ['valid', 'valid-prerelease', 'valid-entity', 'mismatch', 'unsafe-version',
                     'leading-zero-version', 'leading-zero-prerelease',
                     'invalid-date', 'compact-date', 'date-type', 'version-type',
                     'missing-title', 'empty-title', 'title-type', 'missing-message',
                     'missing-cff-version', 'unsupported-cff-version', 'missing-authors',
                     'authors-string', 'author-string', 'unnamed-author', 'empty-author-name',
                     'author-name-type', 'wrong-type', 'non-object']
            with patch.object(release, 'ROOT', root):
                # Run against future releases as well as the checked-out version.
                for version in [current_version, '0.0.2', '2.3.4-rc.1+build.2']:
                    for case in cases:
                        citation = json.loads(original['CITATION.cff'])
                        citation['version'] = version
                        package_version = version
                        if case == 'valid-prerelease':
                            base = re.split(r'[-+]', version, maxsplit=1)[0]
                            citation['version'] = base + '-rc.1+build.2'
                            package_version = citation['version']
                        elif case == 'valid-entity': citation['authors'] = [{'name': 'Example Team'}]
                        elif case == 'mismatch': citation['version'] = '0.0.0' if version != '0.0.0' else '0.0.1'
                        elif case == 'unsafe-version': citation['version'] = '../escape'
                        elif case == 'leading-zero-version': citation['version'] = '00.0.1'
                        elif case == 'leading-zero-prerelease': citation['version'] = '0.0.1-01'
                        elif case == 'invalid-date': citation['date-released'] = '2026-02-30'
                        elif case == 'compact-date': citation['date-released'] = '20261004'
                        elif case == 'date-type': citation['date-released'] = None
                        elif case == 'version-type': citation['version'] = 1
                        elif case in ['missing-title', 'missing-message', 'missing-cff-version']:
                            del citation[case.removeprefix('missing-')]
                        elif case == 'empty-title': citation['title'] = ' '
                        elif case == 'title-type': citation['title'] = []
                        elif case == 'unsupported-cff-version': citation['cff-version'] = '1.1.0'
                        elif case == 'missing-authors': citation['authors'] = []
                        elif case == 'authors-string': citation['authors'] = 'Michael Brackx'
                        elif case == 'author-string': citation['authors'] = ['Michael Brackx']
                        elif case == 'unnamed-author': citation['authors'] = [{}]
                        elif case == 'empty-author-name': citation['authors'] = [{'family-names': ' '}]
                        elif case == 'author-name-type': citation['authors'] = [{'family-names': 1}]
                        elif case == 'wrong-type': citation['type'] = 'dataset'
                        elif case == 'non-object': citation = []
                        (root/'CITATION.cff').write_text(json.dumps(citation))
                        (root/'lakefile.toml').write_text(package_for(package_version))
                        with self.subTest(version=version, case=case):
                            if case.startswith('valid'):
                                self.assertEqual(release.metadata(), citation)
                            else:
                                with self.assertRaises(ValueError): release.metadata()

    def test_release_source_layout_rejects_missing_and_unexpected_files(self):
        with tempfile.TemporaryDirectory(prefix='classical-sources-') as directory:
            root = Path(directory)
            for name in release.ROOT_FILES:
                (root/name).write_text('Fixture source.\n')
            (root/'.lake').mkdir()
            (root/'.lake/private').write_text('Build cache.\n')
            with patch.object(release, 'ROOT', root):
                self.assertEqual({p.name for p in release.source_files()}, release.ROOT_FILES)
                (root/'LICENSE').unlink()
                with self.assertRaises(ValueError): release.source_files()
                (root/'LICENSE').write_text('Fixture source.\n')
                (root/'unexpected.txt').write_text('Unexpected source.\n')
                with self.assertRaises(ValueError): release.source_files()
                (root/'unexpected.txt').unlink()
                (root/'scripts').mkdir()
                (root/'scripts/.env').write_text('Fixture environment file.\n')
                with self.assertRaises(ValueError): release.source_files()
                (root/'scripts/.env').unlink()
                (root/'LICENSE').unlink()
                (root/'LICENSE').symlink_to('README.md')
                with self.assertRaises(ValueError): release.source_files()

    def test_local_proofs_build_without_warnings(self):
        sources = [ROOT/'ClassicalTheorems.lean'] + sorted((ROOT/'ClassicalTheorems').rglob('*.lean'))
        for source in sources:
            relative = source.relative_to(ROOT)
            with self.subTest(source=str(relative)):
                trace = ROOT/'.lake/build/lib/lean'/relative.with_suffix('.trace')
                self.assertTrue(trace.is_file(), f'Build first: missing {relative} trace')
                log = json.loads(trace.read_text())['log']
                warnings = [entry['message'] for entry in log if entry['level'] == 'warning']
                self.assertEqual(warnings, [], '\n'.join(warnings))

    def test_documented_theorems_exist_and_pass_axiom_audit(self):
        indexed = set(re.findall(r'\[`([A-Za-z_][A-Za-z0-9_.]*)`\]\(',
                                 (ROOT/'theorems.md').read_text()))
        self.assertEqual(len(indexed), 10, 'The theorem table must document all ten indexed propositions')
        with tempfile.TemporaryDirectory(prefix='classical-documented-') as directory:
            file = Path(directory)/'Documented.lean'
            file.write_text('import ClassicalTheorems\n'+''.join(
                f"#check_indexed {name}\n"
                for name in sorted(indexed)))
            result = subprocess.run(['lake','env','lean',str(file)],cwd=ROOT,
                                    capture_output=True,text=True,timeout=120)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_audit_rejects_unproved_and_non_propositions(self):
        cases = [
            ('proved', 'theorem checked : True := True.intro\n#check_indexed checked', None),
            ('definition', 'def checked : Nat := 0\n#check_indexed checked', 'is not a proof of a proposition'),
            ('sorry', 'theorem hidden : True := by sorry\ntheorem checked : True := hidden\n#check_indexed checked', 'sorryAx'),
            ('axiom', 'axiom forbidden : False\ntheorem checked : False := forbidden\n#check_indexed checked', 'unapproved axioms'),
        ]
        with tempfile.TemporaryDirectory(prefix='classical-audit-') as directory:
            for name, source, error in cases:
                with self.subTest(case=name):
                    p = Path(directory)/(name+'.lean')
                    p.write_text('import ClassicalTheorems.Audit\n'+source+'\n')
                    r = subprocess.run(['lake','env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=60)
                    if error is None: self.assertEqual(r.returncode,0,r.stdout+r.stderr)
                    else:
                        self.assertNotEqual(r.returncode,0,r.stdout+r.stderr)
                        self.assertIn(error,r.stdout+r.stderr)
if __name__ == '__main__': unittest.main()
