"""Record what a run of run_all.sh was made with: the exact source files, the binary, the build
flags, the tool versions and the machine, and the checksums of the results.

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

Every file is listed with its SHA-256 checksum and with its git blob id. The blob id depends only
on the content of the file, so it is the same in every git repository: `git ls-tree -r HEAD` in a
repository that holds these files shows the same ids, and `git hash-object FILE` recomputes one.
This ties the results to file contents even if the run was not made from a commit.

usage: law_manifest.py out.json ["free text, for example when the run was started" [commit the sources were taken from]]
"""
import sys, os, json, hashlib, platform, subprocess, datetime, importlib.metadata

HERE = os.path.dirname(os.path.abspath(__file__))
SOURCES = ['run_all.sh', 'law_cg.py', 'law_lp.py', 'law_oracle.cpp', 'CMakeLists.txt', 'law_certify.py', 'law_check_iv.py']
OTHER = ['law_oracle_test.py', 'law_manifest.py', '.clang-format', '.clang-tidy']
PERIODS = (16, 32, 64, 128, 256)
PACKAGES = ['numpy', 'scipy', 'highspy', 'python-flint', 'mpmath']


def entry(name):
    path = os.path.join(HERE, name)
    if not os.path.exists(path):
        return None
    data = open(path, 'rb').read()
    mtime = datetime.datetime.fromtimestamp(os.path.getmtime(path)).astimezone().isoformat(timespec='seconds')
    return dict(file=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
                git_blob=hashlib.sha1(b'blob %d\0' % len(data) + data).hexdigest(), modified=mtime)


def command(args):
    try:
        return subprocess.run(args, capture_output=True, text=True, cwd=HERE, timeout=30).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return ''


def first_line(path, key):
    try:
        return next((line.strip() for line in open(path) if key in line), '')
    except OSError:
        return ''


def main():
    out = sys.argv[1]; note = sys.argv[2] if len(sys.argv) > 2 else ''
    source_commit = sys.argv[3] if len(sys.argv) > 3 else ''
    build = os.path.join(HERE, 'build')
    results = [f'law{N}.json' for N in PERIODS] + [f'law{N}_certified.json' for N in PERIODS] \
        + [f'{kind}{N}.log' for kind in ('law', 'certify', 'check') for N in PERIODS]
    tracked = command(['git', 'ls-files', '--error-unmatch'] + SOURCES) != ''
    manifest = dict(
        written=datetime.datetime.now().astimezone().isoformat(timespec='seconds'),
        note=note,
        source_commit=source_commit,                       # as stated by the caller; the blob ids below are computed
        sources=[e for e in map(entry, SOURCES) if e],
        other_files=[e for e in map(entry, OTHER) if e],
        binary=entry(os.path.join('build', 'law_oracle')),
        build=dict(
            compiler=command(['c++', '--version']).split('\n')[0],
            cmake=command(['cmake', '--version']).split('\n')[0],
            build_type=first_line(os.path.join(build, 'CMakeCache.txt'), 'CMAKE_BUILD_TYPE:').split('=')[-1],
            flags_of_build_type=first_line(os.path.join(build, 'CMakeCache.txt'), 'CMAKE_CXX_FLAGS_RELEASE:').split('=', 1)[-1],
            flags=first_line(os.path.join(build, 'CMakeFiles', 'law_oracle.dir', 'flags.make'), 'CXX_FLAGS'),
            defines=first_line(os.path.join(build, 'CMakeFiles', 'law_oracle.dir', 'flags.make'), 'CXX_DEFINES'),
        ),
        python=dict(version=platform.python_version(),
                    packages={p: importlib.metadata.version(p) for p in PACKAGES}),
        machine=dict(architecture=platform.machine(),
                     processor=' / '.join(line.split(':', 1)[1].strip() for line in command(['lscpu']).split('\n')
                                          if line.startswith(('Vendor ID', 'Model name'))),
                     logical_cores=os.cpu_count(), system=platform.platform()),
        git=dict(repository_head=command(['git', 'rev-parse', 'HEAD']),
                 branch=command(['git', 'rev-parse', '--abbrev-ref', 'HEAD']),
                 sources_tracked_in_this_repository=tracked,
                 remark='' if tracked else (
                     'the files are an export of the commit named in source_commit; `git ls-tree -r` of that commit shows the same blob ids'
                     if source_commit else
                     'the sources were not under version control when this was written; the blob ids identify them')),
        results=[e for e in map(entry, results) if e],
    )
    with open(out, 'w') as fh:
        json.dump(manifest, fh, indent=1)
    print(f"{len(manifest['sources'])} source files, binary {manifest['binary']['sha256'][:16] if manifest['binary'] else 'missing'}, "
          f"{len(manifest['results'])} result files; tracked in git: {tracked}")


if __name__ == '__main__':
    main()
