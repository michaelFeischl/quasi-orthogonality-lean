#!/usr/bin/env python3
"""Build all project modules and check the public exports' axioms."""
from pathlib import Path
import re
import subprocess
import tempfile


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    exports = [
        "Autoformalization.PetrovGalerkin.exists_unique_discrete_solution",
        "Autoformalization.PetrovGalerkin.quasi_orthogonality",
        "Autoformalization.PetrovGalerkin.exists_unique_maximal_variance",
        "Autoformalization.PetrovGalerkin.maximalVariance",
        "Autoformalization.PetrovGalerkin.maximalVariance_characterization",
        "Autoformalization.HilbertSequence.quasi_orthogonality",
        "Autoformalization.PetrovGalerkin.petrov_galerkin_assumptions",
    ]
    sources = [root / 'Autoformalization.lean', *sorted((root / 'Autoformalization').rglob('*.lean'))]
    modules = [str(p.relative_to(root).with_suffix('')).replace('/', '.') for p in sources]
    build = str(root / 'scripts/build')
    subprocess.run([build, *modules], cwd=root, check=True)
    # Recheck every module with proof holes treated as errors, including helpers
    # that are not used by the exported theorems. Imports use the build cache.
    for source in sources:
        subprocess.run([build, '--check', '-DwarningAsError=true',
                        '-Dlinter.unusedVariables=false',
                        str(source.relative_to(root))], cwd=root, check=True)
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
    print(f'VERIFIED: {len(modules)} project modules; {len(exports)} public exports; standard axioms only.')


if __name__ == '__main__':
    main()
