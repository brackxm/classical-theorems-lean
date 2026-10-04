#!/usr/bin/env python3
"""Verify release metadata, source layout, builds and proof audits."""
import argparse
from datetime import date
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ROOT_FILES = {
    '.gitignore', 'CITATION.cff', 'LICENSE', 'NOTICE',
    'README.md', 'theorems.md', 'proofs.md',
    'third-party.md',
    'ClassicalTheorems.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
}
SOURCE_DIRS = {'.github', 'ClassicalTheorems', 'scripts', 'vendor'}
EXCLUDED_DIRS = {'.git', '.lake', '__pycache__', 'dist'}


def metadata():
    # JSON is a YAML subset, so this citation file also needs no YAML dependency.
    citation = json.loads((ROOT/'CITATION.cff').read_text())
    package = tomllib.loads((ROOT/'lakefile.toml').read_text())
    if not isinstance(citation, dict):
        raise ValueError('Release citation must be an object')
    for field in ['cff-version', 'message', 'title', 'version', 'date-released']:
        value = citation.get(field)
        if not isinstance(value, str) or not value.strip():
            raise ValueError(f'Release citation needs a nonempty {field} string')
    if citation['cff-version'] != '1.2.0':
        raise ValueError('Release citation must use CFF 1.2.0')
    if citation.get('type') != 'software':
        raise ValueError('Release citation must have software resource type')
    authors = citation.get('authors')
    if not isinstance(authors, list) or not authors:
        raise ValueError('Release citation must have a nonempty authors list')
    for author in authors:
        if (not isinstance(author, dict) or
                not any(field in author for field in ['family-names', 'given-names', 'name']) or
                any(not isinstance(value, str) or not value.strip() for value in author.values())):
            raise ValueError('Each release author must be a named person or entity with nonempty string fields')
    numeric = r'(?:0|[1-9][0-9]*)'
    prerelease = r'(?:0|[1-9][0-9]*|[0-9]*[A-Za-z-][0-9A-Za-z-]*)'
    version_pattern = (rf'{numeric}\.{numeric}\.{numeric}'
                       rf'(?:-{prerelease}(?:\.{prerelease})*)?'
                       r'(?:\+[0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*)?')
    if not re.fullmatch(version_pattern, citation['version']):
        raise ValueError('Release version must be a canonical semantic version')
    publication_date = citation['date-released']
    if date.fromisoformat(publication_date).isoformat() != publication_date:
        raise ValueError('Publication date must have YYYY-MM-DD form')
    if package['version'] != citation['version']:
        raise ValueError('Package and citation versions differ')
    return citation


def source_files():
    files = []
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        base = Path(directory)
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDED_DIRS)
        if base == ROOT:
            unexpected = set(dirs)-SOURCE_DIRS
            if unexpected:
                raise ValueError(f'Unrecognized release directories: {sorted(unexpected)}')
        for name in dirs:
            if (base/name).is_symlink():
                raise ValueError(f'Source directory is a symlink: {base/name}')
        for name in sorted(names):
            if name == '.DS_Store' or name.endswith('.pyc'):
                continue
            path = base/name
            if base == ROOT and name not in ROOT_FILES:
                raise ValueError(f'Unrecognized release file: {name}')
            if path.is_symlink() or not path.is_file():
                raise ValueError(f'Non-regular source file: {path}')
            if name == '.env' or name.startswith('.env.'):
                raise ValueError(f'Environment file in release: {path}')
            files.append(path)
    present = {p.name for p in files if p.parent == ROOT}
    missing = ROOT_FILES - present
    if missing:
        raise ValueError(f'Missing required release files: {sorted(missing)}')
    return sorted(files)


def run_checks():
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    commands = [
        ([sys.executable, 'scripts/check_vendor.py'], ROOT),
        ([sys.executable, 'scripts/check_imports.py'], ROOT),
        ([sys.executable, 'scripts/check_standalone.py'], ROOT),
        (['lake', 'build'], ROOT),
        ([sys.executable, 'scripts/test_checks.py'], ROOT),
    ]
    for command, cwd in commands:
        label = ' '.join(command[1:]) if command[0] == sys.executable else ' '.join(command)
        print(f'Checking {label} ({cwd.relative_to(ROOT)})', flush=True)
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f'{label} failed:\n{result.stdout[-12000:]}')
        lines = result.stdout.strip().splitlines()
        summary = next((line for line in lines if re.fullmatch(r'Ran [0-9]+ tests? in .*', line)), None)
        if summary:
            print(summary, flush=True)
        print(lines[-1] if lines else 'Passed', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--metadata-only', action='store_true', help='Check release metadata and source layout')
    args = parser.parse_args()
    metadata()
    source_files()
    if args.metadata_only:
        print('Release metadata and source layout are consistent.')
        return
    run_checks()


if __name__ == '__main__':
    main()
