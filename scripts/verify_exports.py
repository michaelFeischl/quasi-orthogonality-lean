#!/usr/bin/env python3
"""Build all project modules and check the public manifest exports' axioms."""
from pathlib import Path
import json
import re
import subprocess
import tempfile


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    anchors = json.loads((root / 'docs/frozen-anchor-manifest.json').read_text())['anchors']
    if not anchors or any(a['state'] != 'SEALED' for a in anchors):
        raise SystemExit('Verification requires a nonempty, fully sealed manifest.')
    exports = [a['export'] for a in anchors]
    if len(set(exports)) != len(exports) or any(
        not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', name)
        for name in exports
    ):
        raise SystemExit('Invalid or duplicate export name.')
    sources = [root / 'Autoformalization.lean', *sorted((root / 'Autoformalization').rglob('*.lean'))]
    modules = [str(p.relative_to(root).with_suffix('')).replace('/', '.') for p in sources]
    build = str(root / 'scripts/build')
    subprocess.run([build, *modules], cwd=root, check=True)
    scratch = root / '.scratch'
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='verify_', dir=scratch) as directory:
        probe = Path(directory) / 'Exports.lean'
        probe.write_text('module\nimport Autoformalization\n' + ''.join(
            f'#check @{name}\n#print axioms {name}\n' for name in exports
        ))
        result = subprocess.run([build, '--check', str(probe.relative_to(root))],
                                cwd=root, text=True, capture_output=True)
        print(result.stdout, end='')
        print(result.stderr, end='')
        result.check_returncode()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name in exports:
        matches = re.findall(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        if len(matches) != 1:
            raise SystemExit(f'Missing or ambiguous axiom output for {name}')
        axioms = {a.strip() for a in matches[0].split(',') if a.strip()}
        if not axioms <= allowed:
            raise SystemExit(f'Unexpected axioms for {name}: {sorted(axioms - allowed)}')
    print(f'VERIFIED: {len(modules)} project modules; {len(exports)} sealed public exports; standard axioms only.')


if __name__ == '__main__':
    main()
