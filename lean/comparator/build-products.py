#!/usr/bin/env python3
"""Transfer verified build deltas between jobs in one run; no previous-run cache required."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, shutil, tarfile

root = Path(__file__).resolve().parents[2]
build = root/'lean/.lake/build'

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            digest.update(block)
    return digest.hexdigest()

def identity():
    return {name: os.environ[name] for name in ['GITHUB_SHA', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT']} | {
        'source_manifest_sha256': sha(root/'SOURCE-MANIFEST.json'),
        'lean_toolchain': (root/'lean/lean-toolchain').read_text().strip()}

def snapshot():
    files = {}
    if build.exists():
        for path in sorted(build.rglob('*')):
            if path.is_symlink():
                raise SystemExit('Unexpected build symlink: '+str(path))
            if path.is_file():
                files[path.relative_to(root).as_posix()] = sha(path)
    return files

def safe_path(name):
    path = PurePosixPath(name)
    if path.is_absolute() or '..' in path.parts or path.parts[:3] != ('lean', '.lake', 'build'):
        raise SystemExit('Unsafe build artifact path: '+name)
    resolved = (root/name).resolve()
    if not resolved.is_relative_to(build.resolve()):
        raise SystemExit('Build artifact path escaped output directory')
    return resolved

def metadata(directory, stage):
    return directory/f'build-stage-{stage}.json'

def archive(directory, stage):
    return directory/f'build-stage-{stage}.tar.gz'

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('mode', choices=['snapshot', 'pack', 'restore'])
parser.add_argument('--directory', type=Path, required=True)
parser.add_argument('--stage', type=int, choices=range(0, 7), required=True)
parser.add_argument('--state', type=Path)
args = parser.parse_args()
args.directory.mkdir(parents=True, exist_ok=True)
if args.mode == 'snapshot':
    if args.state is None:
        parser.error('snapshot requires --state')
    args.state.write_text(json.dumps(snapshot(), sort_keys=True)+'\n')
    print('Saved pre-build file identities')
elif args.mode == 'pack':
    if args.stage == 0 or args.state is None:
        parser.error('pack requires stage 1..6 and --state')
    receipt = root/f'build-stage-{args.stage}-receipt/status.txt'
    if receipt.read_text() != 'PASS\n':
        raise SystemExit('Cannot publish products from an unfinished or failed batch')
    previous = json.loads(args.state.read_text())
    current = snapshot()
    changed = {name: value for name, value in current.items() if previous.get(name) != value}
    removed = sorted(set(previous)-set(current))
    parents = {str(i): sha(archive(args.directory, i)) for i in range(1, args.stage)}
    output = archive(args.directory, args.stage)
    with tarfile.open(output, 'w:gz', compresslevel=1) as bundle:
        for name in changed:
            bundle.add(safe_path(name), arcname=name, recursive=False)
    report = identity() | {'schema': 1, 'stage': args.stage, 'status': 'PASS',
        'archive_sha256': sha(output), 'previous_archive_sha256': parents,
        'changed_files_sha256': changed, 'removed_files': removed}
    metadata(args.directory, args.stage).write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    print('Packed stage', args.stage, ':', len(changed), 'changed files,', output.stat().st_size, 'bytes')
else:
    expected = identity()
    hashes = {}
    for stage in range(1, args.stage+1):
        report = json.loads(metadata(args.directory, stage).read_text())
        if any(report.get(name) != value for name, value in expected.items()):
            raise SystemExit('Build artifact belongs to another commit, run, attempt or source manifest')
        if report['stage'] != stage or report['status'] != 'PASS' or report['previous_archive_sha256'] != hashes:
            raise SystemExit('Incomplete or inconsistent build artifact chain')
        packed = archive(args.directory, stage)
        digest = sha(packed)
        if digest != report['archive_sha256']:
            raise SystemExit('Build artifact checksum differs')
        hashes[str(stage)] = digest
        for name in report['removed_files']:
            path = safe_path(name)
            path.unlink(missing_ok=True)
        with tarfile.open(packed, 'r:gz') as bundle:
            members = bundle.getmembers()
            names = [member.name for member in members]
            if len(names) != len(set(names)) or set(names) != set(report['changed_files_sha256']):
                raise SystemExit('Unexpected or duplicate files in build artifact')
            for member in members:
                safe_path(member.name)
                if not member.isfile():
                    raise SystemExit('Only regular build product files may be restored')
            for member in members:
                destination = safe_path(member.name)
                destination.parent.mkdir(parents=True, exist_ok=True)
                stream = bundle.extractfile(member)
                if stream is None:
                    raise SystemExit('Missing regular file data in build artifact')
                with stream, destination.open('wb') as output:
                    shutil.copyfileobj(stream, output)
                destination.chmod(member.mode & 0o777)
                os.utime(destination, (member.mtime, member.mtime))
        for name, digest in report['changed_files_sha256'].items():
            if sha(safe_path(name)) != digest:
                raise SystemExit('Restored build product checksum differs: '+name)
    print('PASS: restored', args.stage, 'build stages from this exact workflow run')
