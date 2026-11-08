#!/usr/bin/env python3
"""Build the archived proof sources and audit the exact manuscript statements.

Run `lake exe cache get` first. Only Mathlib/dependency caches are required.
The default run recompiles every project module; --resume accepts only objects
whose source, dependency fingerprints, compiler version and object hash match.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / 'build'
LOGS = BUILD / 'logs'
LIB = ROOT / '.lake/build/lib/lean'
STATE = BUILD / 'compile-state.json'
MATHLIB = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
ROOTS = ['ManuscriptCorrespondence', 'JSP001040FinalAudit']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(source):
    out, i, depth, string = [], 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif string:
            if source[i] == '\\' and i + 1 < len(source):
                out.extend('  '); i += 2
            else:
                if source[i] == '"': string = False
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif source.startswith('--', i):
            j = source.find('\n', i)
            if j < 0: j = len(source)
            out.extend(' ' * (j - i)); i = j
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif source[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(source[i]); i += 1
    assert depth == 0 and not string, 'Unterminated comment or string'
    return ''.join(out)


def run(command, logfile, env):
    with logfile.open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        print(logfile.read_text()[-12000:], file=sys.stderr, flush=True)
        raise RuntimeError(f'{command[0]} failed ({result.returncode}): {logfile}')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    assert args.jobs >= 1
    LOGS.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_PATH'] = subprocess.check_output(
        ['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    env['LEAN_PATH'] = str(LIB) + os.pathsep + env['LEAN_PATH']
    lean = shutil.which('lean')
    assert lean, 'Install the pinned Lean toolchain and add it to PATH'
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.34.1,' in version, version
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    assert next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib') == MATHLIB
    mathlib_head = subprocess.check_output(
        ['git', '-C', str(ROOT / '.lake/packages/mathlib'), 'rev-parse', 'HEAD'],
        text=True).strip()
    assert mathlib_head == MATHLIB, mathlib_head

    sources = {}
    for base in ['OAI', 'RestrictionWork', 'SphereAreaReuse', 'LeanOscillatory']:
        for path in (ROOT / base).rglob('*.lean'):
            sources[path.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.')] = path
    for path in ROOT.glob('*.lean'):
        if path.name != 'lakefile.lean': sources[path.stem] = path
    imports, forbidden = {}, []
    pattern = re.compile(r'\b(?:sorry|admit|axiom|unsafe|native_decide|skipKernelTC|run_cmd|run_elab)\b|Lean\.modifyEnv')
    for module, path in sorted(sources.items()):
        code = code_only(path.read_text())
        imports[module] = [item for row in re.findall(
            r'^\s*(?:public\s+|private\s+)?import\s+([^\n]+)', code, re.M)
            for item in row.split()]
        for match in pattern.finditer(code):
            forbidden.append({'path': path.relative_to(ROOT).as_posix(),
                              'line': code.count('\n', 0, match.start()) + 1,
                              'token': match.group()})
    assert not forbidden, forbidden
    baseline = json.loads((ROOT / 'provenance/MigrationBaseline.json').read_text())
    unchanged = all(sha(ROOT / name) == value for name, value in baseline['sources'].items())
    paper = ROOT / 'paper/Sphere_Fourier_Extension_ArXiv.tex'
    paper_unchanged = sha(paper) == baseline['paper_sha256']

    reachable, external = set(), set()
    def visit(module):
        if module in reachable: return
        if module not in sources:
            external.add(module); return
        reachable.add(module)
        for dep in imports[module]: visit(dep)
    for root in ROOTS: visit(root)
    for module in external:
        assert module.split('.')[0] in {'Mathlib', 'Lean', 'Init', 'Std', 'Batteries',
                                       'Aesop', 'Qq', 'ProofWidgets', 'ImportGraph'}, module
    assert reachable == set(sources), sorted(set(sources) - reachable)
    deps = {m: set(imports[m]) & reachable for m in reachable}
    signatures = {}
    def signature(module, visiting=frozenset()):
        if module in signatures: return signatures[module]
        assert module not in visiting, f'Import cycle: {module}'
        data = [version, MATHLIB, sha(sources[module])]
        data += [signature(dep, visiting | {module}) for dep in sorted(deps[module])]
        signatures[module] = hashlib.sha256('\n'.join(data).encode()).hexdigest()
        return signatures[module]
    for module in reachable: signature(module)
    old = json.loads(STATE.read_text()) if args.resume and STATE.exists() else {}
    done = {}
    if not args.resume:
        for folder in ['OAI', 'RestrictionWork', 'SphereAreaReuse', 'LeanOscillatory']:
            shutil.rmtree(LIB / folder, ignore_errors=True)
        for path in sources.values():
            if path.parent == ROOT:
                for extension in ['.olean', '.ilean', '.olean.private', '.olean.server', '.ir']:
                    (LIB / (path.stem + extension)).unlink(missing_ok=True)
    else:
        for module in sorted(reachable):
            obj = LIB / (module.replace('.', '/') + '.olean')
            row = old.get(module, {})
            if (row.get('signature') == signatures[module] and obj.exists()
                    and row.get('object_sha256') == sha(obj)):
                done[module] = row
        while any(not deps[m] <= done.keys() for m in done):
            done = {m: row for m, row in done.items() if deps[m] <= done.keys()}
    def checkpoint():
        temp = STATE.with_suffix('.tmp')
        temp.write_text(json.dumps(done, indent=2) + '\n'); temp.replace(STATE)
    def compile_one(module):
        started = time.monotonic()
        target = LIB / module.replace('.', '/')
        target.parent.mkdir(parents=True, exist_ok=True)
        log = LOGS / (module + '.log')
        run([lean, '-DautoImplicit=false', '-j1',
             '-o', str(target) + '.olean', '-i', str(target) + '.ilean',
             str(sources[module].relative_to(ROOT))], log, env)
        return {'signature': signatures[module], 'object_sha256': sha(Path(str(target) + '.olean')),
                'seconds': round(time.monotonic() - started, 3), 'exit_code': 0}
    print(f'Verified source hygiene: {len(sources)} files; {len(done)} matching build objects.', flush=True)
    remaining = reachable - done.keys()
    running = {}
    start = time.monotonic()
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while remaining or running:
                ready = sorted(m for m in remaining if deps[m] <= done.keys())
                for module in ready[:args.jobs - len(running)]:
                    remaining.remove(module); running[pool.submit(compile_one, module)] = module
                assert running, 'Unresolved dependencies'
                finished, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in finished:
                    module = running.pop(future)
                    done[module] = future.result()
                    print(f'[{len(done)}/{len(reachable)}] {module}', flush=True)
                checkpoint()
    finally:
        checkpoint()
    print(f'Compilation complete in {time.monotonic() - start:.1f}s.', flush=True)

    audits = {}
    for module in ['ManuscriptStatement', 'ManuscriptCorrespondence', 'JSP001040FinalAudit']:
        log = LOGS / (module + '.audit.log')
        run([lean, '-DautoImplicit=false', '-j1', module + '.lean'], log, env)
        expected = re.findall(r'^#print axioms (\S+)', (ROOT / (module + '.lean')).read_text(), re.M)
        rows = re.findall(r"^'(.*?)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",
                          log.read_text(), re.M)
        assert [name for name, _ in rows] == expected, (module, len(rows), len(expected))
        parsed = {name: sorted({a.strip().split('.{')[0] for a in names.split(',') if a.strip()})
                  for name, names in rows}
        assert all(set(names) <= ALLOWED for names in parsed.values()), parsed
        audits[module] = parsed
        print(f'Axiom audit passed: {module}: {len(parsed)} declarations.', flush=True)
    replays = {}
    for module in ['ManuscriptStatement', 'RestrictionWork.JSP001040CatalogStatement']:
        run(['leanchecker', '-v', module], LOGS / (module + '.kernel.log'), env)
        replays[module] = 0
        print(f'Kernel replay passed: {module}', flush=True)
    try:
        commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    except subprocess.CalledProcessError:
        commit = None
    record = {'lean': version, 'mathlib_commit': mathlib_head, 'git_commit': commit,
              'time_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
              'project_modules': len(sources), 'compiled_modules': len(done),
              'source_hygiene_hits': forbidden, 'proof_sources_unchanged': unchanged,
              'paper_unchanged': paper_unchanged, 'paper_sha256': sha(paper),
              'allowed_axioms': sorted(ALLOWED), 'axiom_audits': audits,
              'kernel_replay_exit_codes': replays, 'result': 'passed'}
    (BUILD / 'Verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k != 'axiom_audits'}, indent=2), flush=True)


if __name__ == '__main__':
    main()
