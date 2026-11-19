#!/usr/bin/env python3
"""Read-only campaign lint. This is not a Lean parser or a kernel replay."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

VENDORED = Path(__file__).resolve().parent / 'vendor/check_frozen_anchors.py'
VENDORED_SHA256 = '634ae87ae198056277e6b50448d144a967ee04f8e6cd86635fd420d079521a7f'
PIN_HASHES = {
    'lakefile.toml': '4d41e162fd760780b547d26d431363b1d6b2150aebca0d9ce74c540ac88cce4d',
    'lake-manifest.json': '1da68f7359d0d636ab81789410363039935e4fa7ee50f23d563c4951610a6a80',
    'lean-toolchain': '582a63f8f9c5128067b688778c1051cf1464c3ca9d57b9325025c051c29b774a',
}
MODULE = r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*'
IMPORT_LINE = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(' + MODULE + r'(?:[ \t]+' + MODULE + r')*)\s*$')
FORBIDDEN = re.compile(r'\b(?:elab|elab_rules|macro|macro_rules|syntax|run_cmd|run_elab|run_meta|run_tac|by_elab|addDecl|axiom|constant|sorryAx)\b|\bset_option\s+«?debug»?\s*\.')
# These built-in contextual interpolators have no bang immediately before the
# literal, so masking their strings would have the same executable-content gap.
CONTEXT_INTERPOLATION = re.compile(r'\b(?:dbg_trace|throwError|throwErrorAt|throwNamedError|throwNamedErrorAt|logNamedError|logNamedErrorAt|logNamedWarning|logNamedWarningAt)\b|\b(?:Macro\.)?(?:trace|trace_goal)\s*\[')
REGISTER = re.compile(r'(?:@\s*\[|\battribute\s*\[)[^\]]*\b(?:command_elab|term_elab|tactic|macro)\b', re.S)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_vendored():
    if digest(VENDORED) != VENDORED_SHA256:
        raise ValueError('vendored frozen guard changed; review its successor before updating the guard pin')
    spec = importlib.util.spec_from_file_location('vendored_frozen_guard', VENDORED)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


BASE = load_vendored()


def code_mask(text: str) -> str:
    """Mask nested comments and literals, without swallowing Lean name quotations.

    The installed mask accepts an unbounded apostrophe-delimited region; Lean's
    `'foo` name quotations must instead remain visible to the policy lint.
    """
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end == -1 else end
        elif text.startswith('/-', i):
            depth, i = 1, i + 2
            while i < len(text) and depth:
                if text.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif text.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated block comment')
        elif text[i] == '"':
            # Prefixed strings may contain arbitrary executable interpolations.
            # Reject all bang prefixes (s!, m!, f!, custom names), including
            # whitespace/comments before the quote, and attached raw/custom
            # prefixes. Ordinary unprefixed literal strings remain inert.
            prefix = ''.join(out[:i])
            if re.search(r"[\w'.«»]+!\s*$", prefix) or (
                i and (text[i - 1].isalnum() or text[i - 1] in "_!#'«»")
            ):
                raise ValueError('unsupported prefixed string: executable interpolation cannot be masked')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError('unterminated string literal')
        elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
            match = re.match(r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.))'", text[i:])
            if match is None:
                i += 1
                continue
            i += len(match.group())
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if out[j] != '\n':
                out[j] = ' '
    return ''.join(out)


class CampaignGuard(BASE.Guard):
    code_mask = staticmethod(code_mask)

    def project_files(self) -> list[Path]:
        files = []
        for directory, dirs, names in os.walk(self.root, followlinks=False):
            dirs[:] = [d for d in dirs if d not in {'.git', '.lake', '.venv', '.agents', '.codex', '__pycache__'}]
            for d in dirs:
                if (Path(directory) / d).is_symlink():
                    self.fail(f'project directory symlink is unsupported: {Path(directory) / d}')
            files.extend(Path(directory) / name for name in names if name.endswith('.lean'))
        return sorted(files)

    def imports_text(self, text: str) -> set[str]:
        imports = set()
        for line in self.code_mask(text).splitlines():
            if re.search(r'\bimport\b', line):
                match = IMPORT_LINE.fullmatch(line)
                if match is None:
                    raise ValueError('unsupported import syntax: use complete one-line import commands')
                imports.update(match.group(1).split())
        return imports

    def comparator_challenges(self) -> set[Path]:
        # This campaign authorizes only manifest-bound draft proof regions.
        return set()

    def campaign(self, manifest: dict, *, dependencies: bool = True) -> None:
        self.check(manifest)
        files = self.project_files()
        owners: dict[str, list[Path]] = {}
        for path in files:
            relative = path.relative_to(self.root)
            if path.is_symlink():
                self.fail(f'project Lean symlink is unsupported: {relative}')
            text = self.read_utf8(path)
            if not BASE.has_module_header(text):
                self.fail(f'missing module header: {relative}')
            code = self.code_mask(text)
            self.check_declaration_layout(code, relative)
            for regex in (FORBIDDEN, REGISTER, CONTEXT_INTERPOLATION):
                for match in regex.finditer(code):
                    line = code.count('\n', 0, match.start()) + 1
                    self.fail(f'forbidden construct {match.group()!r}: {relative}:{line}')
            for _, _, _, export in self.declarations(text):
                if export:
                    owners.setdefault(export, []).append(path)
        for anchor in manifest['anchors']:
            export = anchor['export']
            if owners.get(export) != [self.root / anchor['path']]:
                self.fail(f'frozen export must have one unique owner: {export}')
            implementation = anchor.get('implementation')
            if implementation:
                providers = owners.get(implementation['export'], [])
                expected = self.root / (implementation['module'].replace('.', '/') + '.lean')
                if any(path != expected for path in providers) or len(providers) > 1:
                    self.fail(f'provider export has unauthorized owner: {implementation["export"]}')
        self.check_pins_sources(manifest)
        packages = json.loads((self.root / 'lake-manifest.json').read_text())['packages']
        if dependencies:
            self.check_dependencies(packages)
        self.check_production_imports(packages)

    def check_declaration_layout(self, code: str, relative: Path) -> None:
        """Keep ownership parsing within its audited line-oriented grammar.

        A command scoped with `open ... in` or `set_option ... in` must put its
        declaration on the next line. Namespace/section boundaries must occupy
        an entire line so the installed namespace stack cannot miss commands.
        """
        declaration = re.compile(r"(?<![\w.'«])(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|example)(?![\w.'»])")
        boundary = re.compile(r"(?<![\w.'«])(?:namespace|section|end)(?![\w.'»])")
        for number, line in enumerate(code.splitlines(), 1):
            parsed = BASE.DECL.match(line)
            if parsed:
                name = parsed.group(3)
                if name is None and parsed.group(2) not in {'instance', 'example'}:
                    self.fail(f'unsupported declaration name: {relative}:{number}; use an ordinary ASCII identifier')
                elif name is not None:
                    tail = line[parsed.end(3):]
                    if tail and not (tail[0].isspace() or tail[0] in '({[:'):
                        self.fail(f'unsupported declaration name: {relative}:{number}; use an ordinary ASCII identifier')
            for token in declaration.finditer(line):
                if parsed is None or token.start() != parsed.start(2):
                    self.fail(f'unsupported scoped declaration formatting: {relative}:{number}; put the declaration on its own line')
            for token in boundary.finditer(line):
                word = token.group()
                valid = (re.fullmatch(r'\s*namespace\s+' + MODULE + r"\s*", line)
                         if word == 'namespace' else BASE.SECTION.fullmatch(line)
                         if word == 'section' else BASE.END.fullmatch(line))
                if valid is None:
                    self.fail(f'unsupported namespace/section boundary formatting: {relative}:{number}')

    def check_pins_sources(self, manifest: dict) -> None:
        for name, expected in PIN_HASHES.items():
            if digest(self.root / name) != expected:
                self.fail(f'dependency/config pin drift: {name}')
        if (self.root / 'lakefile.lean').exists():
            self.fail('unapproved lakefile.lean can override the pinned TOML configuration')
        config = tomllib.loads((self.root / 'lakefile.toml').read_text())
        if config.get('lean_lib') != [{'name': 'Autoformalization'}]:
            self.fail('unapproved lean_lib configuration')
        for anchor in manifest['anchors']:
            source = anchor['source']
            name = source['range'].split(':', 1)[0]
            path = (self.root / name).resolve()
            if not path.is_relative_to(self.root / 'sources'):
                self.fail(f'source path outside sources: {name}')
            elif source['revision'] != 'sha256:' + digest(path):
                self.fail(f'source revision drift: {name}')

    def check_dependencies(self, packages: list[dict]) -> None:
        for package in packages:
            path = self.root / '.lake/packages' / package['name']
            if not path.is_dir() or path.is_symlink():
                self.fail(f'missing or symlinked pinned dependency: {package["name"]}')
                continue
            def git(*args: str) -> subprocess.CompletedProcess:
                return subprocess.run(['git', '--no-optional-locks', '-C', str(path), *args], text=True, capture_output=True)
            head = git('rev-parse', 'HEAD')
            status = git('status', '--porcelain', '--untracked-files=all')
            if head.returncode or head.stdout.strip() != package['rev']:
                self.fail(f'dependency revision drift: {package["name"]}')
            if status.returncode or status.stdout.strip():
                self.fail(f'dependency source tree dirty: {package["name"]}')

    def check_production_imports(self, packages: list[dict]) -> None:
        modules = {self.module_name(path): path for path in self.project_files()}
        roots = [self.root / '.lake/packages' / package['name'] for package in packages]
        tracked = {}
        for root in roots:
            result = subprocess.run(['git', '--no-optional-locks', '-C', str(root), 'ls-files', '-z'], capture_output=True, text=True)
            tracked[root] = set(result.stdout.split('\0')) if result.returncode == 0 else set()
        prefix = subprocess.run(['lean', '--print-prefix'], cwd=self.root,
                                capture_output=True, text=True)
        if prefix.returncode or not prefix.stdout.strip():
            self.fail('cannot locate the pinned Lean toolchain; install elan and run from the project')
            return
        toolchain = Path(prefix.stdout.strip()) / 'src/lean'
        roots.append(toolchain)
        todo, seen = ['Autoformalization'], set()
        while todo:
            module = todo.pop()
            if module in seen:
                continue
            seen.add(module)
            path = modules.get(module)
            if path is None:
                self.fail(f'missing production module: {module}')
                continue
            if not (module == 'Autoformalization' or module.startswith('Autoformalization.')):
                self.fail(f'production imports unapproved project root: {module}')
            for imported in self.imports(path):
                if imported in modules:
                    todo.append(imported)
                elif imported.startswith('Autoformalization.'):
                    self.fail(f'missing project import: {module} -> {imported}')
                elif not any((root / (imported.replace('.', '/') + '.lean')).is_file()
                             and (root == toolchain or imported.replace('.', '/') + '.lean' in tracked[root])
                             for root in roots):
                    self.fail(f'import outside pinned external packages: {module} -> {imported}')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    guard = CampaignGuard(args.root)
    try:
        manifest = json.loads((guard.root / 'docs/frozen-anchor-manifest.json').read_text())
        guard.campaign(manifest)
    except (OSError, ValueError, KeyError, TypeError) as error:
        guard.fail(f'cannot validate campaign: {error}')
    if guard.errors:
        print('CAMPAIGN GUARD FAILED:', file=sys.stderr)
        for error in dict.fromkeys(guard.errors):
            print(f'- {error}', file=sys.stderr)
        return 1
    print('CAMPAIGN GUARD OK')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
