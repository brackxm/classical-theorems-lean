#!/usr/bin/env python3
"""Check source imports without relying on ignored build caches."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def imports(text):
    cleaned = []
    i = depth = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif not depth and text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            if not depth or text[i] == '\n':
                cleaned.append(text[i])
            i += 1
    return [module for match in re.finditer(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',
        ''.join(cleaned), re.M) for module in match.group(1).split()]

def main():
    records = [(p.parent, json.loads(p.read_text()))
               for p in sorted((ROOT/'vendor').glob('*/upstream.json'))]
    roots = [ROOT] + [d for d, _ in records]
    sources = list((ROOT/'ClassicalTheorems').rglob('*.lean')) + [ROOT/'ClassicalTheorems.lean']
    sources += [d/p for d, r in records for p in r['local_sha256']
                if p.endswith('.lean')]
    external = ('Mathlib', 'Lean', 'Init', 'Batteries', 'Aesop', 'Qq',
                'ProofWidgets', 'Plausible', 'ImportGraph', 'LeanSearchClient')
    for p in sources:
        for m in imports(p.read_text()):
            if m.split('.')[0] in external:
                continue
            rel = m.replace('.', '/')+'.lean'
            assert any((d/rel).is_file() for d in roots), (p, m)
    print(f'Checked import closure for {len(sources)} Lean source files without build-cache lookup.')

if __name__ == '__main__':
    main()
