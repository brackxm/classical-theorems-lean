#!/usr/bin/env python3
"""Check relocatable dependencies, self-contained cache links and source layout."""
import json
import os
import re
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def check_layout(root):
    root = root.resolve()
    configs = [root/'lakefile.toml']
    configs += sorted((root/'vendor').glob('*/lakefile.toml'))
    for file in configs:
        config = tomllib.loads(file.read_text())
        for dep in config.get('require', []):
            if 'path' in dep:
                assert not Path(dep['path']).is_absolute(), (file, dep)
                assert (file.parent/dep['path']).resolve().is_relative_to(root), (file, dep)
        lock = json.loads(file.with_name('lake-manifest.json').read_text())
        assert not Path(lock['packagesDir']).is_absolute(), file
        assert (file.parent/lock['packagesDir']).resolve().is_relative_to(root), file
        for dep in lock['packages']:
            if dep['type'] == 'path':
                assert not Path(dep['dir']).is_absolute(), (file, dep)
                assert (file.parent/dep['dir']).resolve().is_relative_to(root), (file, dep)
    released = 0
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {'.git', '__pycache__', 'dist'}]
        base = Path(directory)
        for name in dirs + files:
            path = base/name
            if path.is_symlink():
                assert not Path(os.readlink(path)).is_absolute(), path
                assert path.resolve(strict=True).is_relative_to(root), path
        if '.lake' in base.relative_to(root).parts:
            continue
        for name in files:
            if name == '.DS_Store':
                continue
            path = base/name
            try:
                source = path.read_text()
            except UnicodeError:
                continue
            assert not re.search(r'\b(?:6|8|100)-theorems\b', source, re.IGNORECASE), path
            assert 'Hundred'+'Theorems' not in source, path
            assert 'Theorems'+str(100) not in source, path
            released += 1
    return len(configs), released


def main():
    configs, released = check_layout(ROOT)
    print(f'Checked {configs} relocatable package configurations and {released} release files; '
          'all cache links remain inside the project.')


if __name__ == '__main__':
    main()
