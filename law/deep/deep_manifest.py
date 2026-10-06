"""Record what a run of run_deep.sh was made with: the exact source files, the binary, the build
flags, the tool versions and the machine, the law it started from, and the checksums of the
results. The form is that of ../law_manifest.py, whose functions are used; file names are
relative to the folder of the law programs (the parent of this folder).

Written by Kristian Muri Knausgård <kristianmk@ieee.org>.
AI assistance: this file was drafted with Claude (Anthropic), an AI system, under the direction
of the author, who is responsible for its content.

usage: deep_manifest.py out.json ["free text, for example when the run was started" [commit the sources were taken from]]
"""
import sys, os, json, platform, datetime, importlib.metadata

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import law_manifest as first

SOURCES = ['deep/run_deep.sh', 'deep/law_deep.py', 'deep/law_deep.cpp', 'deep/CMakeLists.txt',
           'law_cg.py', 'law_lp.py', 'law_certify.py', 'law_check_iv.py']
OTHER = ['deep/law_deep_test.py', 'deep/deep_manifest.py', 'deep/.clang-format', 'deep/.clang-tidy', 'law_oracle_test.py']
START = 'law256.json'
RESULTS = ['deep/law256_deep.json', 'deep/law256_deep_certified.json', 'deep/law256_deep.log',
           'deep/certify256_deep.log', 'deep/check256_deep.log']


def main():
    out = sys.argv[1]; note = sys.argv[2] if len(sys.argv) > 2 else ''
    source_commit = sys.argv[3] if len(sys.argv) > 3 else ''
    build = os.path.join(HERE, 'build')
    tracked = first.command(['git', 'ls-files', '--error-unmatch'] + SOURCES) != ''
    manifest = dict(
        written=datetime.datetime.now().astimezone().isoformat(timespec='seconds'),
        note=note,
        source_commit=source_commit,                       # as stated by the caller; the blob ids below are computed
        sources=[e for e in map(first.entry, SOURCES) if e],
        other_files=[e for e in map(first.entry, OTHER) if e],
        start=first.entry(START),                          # the law of the first stage
        binary=first.entry(os.path.join('deep', 'build', 'law_deep')),
        build=dict(
            compiler=first.command(['c++', '--version']).split('\n')[0],
            cmake=first.command(['cmake', '--version']).split('\n')[0],
            build_type=first.first_line(os.path.join(build, 'CMakeCache.txt'), 'CMAKE_BUILD_TYPE:').split('=')[-1],
            flags_of_build_type=first.first_line(os.path.join(build, 'CMakeCache.txt'), 'CMAKE_CXX_FLAGS_RELEASE:').split('=', 1)[-1],
            flags=first.first_line(os.path.join(build, 'CMakeFiles', 'law_deep.dir', 'flags.make'), 'CXX_FLAGS'),
            defines=first.first_line(os.path.join(build, 'CMakeFiles', 'law_deep.dir', 'flags.make'), 'CXX_DEFINES'),
        ),
        python=dict(version=platform.python_version(),
                    packages={p: importlib.metadata.version(p) for p in first.PACKAGES}),
        machine=dict(architecture=platform.machine(),
                     processor=' / '.join(line.split(':', 1)[1].strip() for line in first.command(['lscpu']).split('\n')
                                          if line.startswith(('Vendor ID', 'Model name'))),
                     logical_cores=os.cpu_count(), system=platform.platform()),
        git=dict(repository_head=first.command(['git', 'rev-parse', 'HEAD']),
                 branch=first.command(['git', 'rev-parse', '--abbrev-ref', 'HEAD']),
                 sources_tracked_in_this_repository=tracked,
                 remark='' if tracked else (
                     'the files are an export of the commit named in source_commit; `git ls-tree -r` of that commit shows the same blob ids'
                     if source_commit else
                     'the sources were not under version control when this was written; the blob ids identify them')),
        results=[e for e in map(first.entry, RESULTS) if e],
    )
    with open(out, 'w') as fh:
        json.dump(manifest, fh, indent=1)
    print(f"{len(manifest['sources'])} source files, binary {manifest['binary']['sha256'][:16] if manifest['binary'] else 'missing'}, "
          f"start {manifest['start']['sha256'][:16] if manifest['start'] else 'missing'}, {len(manifest['results'])} result files; tracked in git: {tracked}")


if __name__ == '__main__':
    main()
