#!/usr/bin/env python3
"""Verify the retained source closure, license integrity and shared pins."""
import hashlib
import json
import tomllib
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent


def check_package_pins(directory, toolchain, mathlib_revision):
    assert (directory/'lean-toolchain').read_text().strip() == toolchain, directory
    config = tomllib.loads((directory/'lakefile.toml').read_text())
    lock = json.loads((directory/'lake-manifest.json').read_text())
    assert config['name'] == lock['name'], directory
    pins = {p['name'].strip('«»'): p for p in lock['packages']}
    for dep in config.get('require', []):
        pin = pins[dep['name']]
        assert not pin['inherited'], dep
        if 'path' in dep:
            assert pin['type'] == 'path', dep
            assert (directory/dep['path']).resolve() == (directory/pin['dir']).resolve(), dep
        else:
            assert pin['type'] == 'git', dep
            assert dep['rev'] == pin['rev'], dep
            assert dep['git'].removesuffix('.git') == pin['url'].removesuffix('.git'), dep
        if dep['name'] == 'mathlib':
            assert dep['rev'] == mathlib_revision, dep


def main():
    records = [(p.parent, json.loads(p.read_text()))
               for p in sorted((ROOT/'vendor').glob('*/upstream.json'))]
    config = tomllib.loads((ROOT/'lakefile.toml').read_text())
    revision = next(dep['rev'] for dep in config['require'] if dep['name'] == 'mathlib')
    count = 0
    for d, r in records:
        assert r['id'] == d.name, d
        assert r['target_toolchain'] == (ROOT/'lean-toolchain').read_text().strip(), d
        assert r['target_mathlib_revision'] == revision, d
        changed = []
        for rel, digest in r['local_sha256'].items():
            p = d/rel
            assert p.resolve().is_relative_to(d.resolve()), p
            assert hashlib.sha256(p.read_bytes()).hexdigest() == digest, p
            if rel in r['upstream_sha256'] and digest != r['upstream_sha256'][rel]:
                changed.append(rel)
            count += 1
        assert sorted(changed) == sorted(r['modified_files']), d
        for rel in r['license_files']:
            assert r['local_sha256'][rel] == r['upstream_sha256'][rel], rel
        actual = {str(p.relative_to(d)) for p in d.rglob('*.lean') if '.lake' not in p.relative_to(d).parts}
        assert actual == {p for p in r['local_sha256'] if p.endswith('.lean')}, d
    packages = [ROOT] + [d for d, _ in records]
    toolchain = (ROOT/'lean-toolchain').read_text().strip()
    for directory in packages:
        check_package_pins(directory, toolchain, revision)
    print(f'Checked {len(records)} supporting packages and {count} file hashes; '
          f'dependency pins agree across {len(packages)} packages.')


if __name__ == '__main__':
    main()
