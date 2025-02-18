#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
A tool for uploading GHC's core libraries to Hackage.

This is a utility for preparing and uploading source distributions and
documentation of GHC's core libraries to Hackage. This should be run in
a GHC tree of the release commit after having run ./configure.

There are two modes, preparation and upload.

* The `prepare` mode takes a link to a bindist and creates a folder containing the
  source and doc tarballs ready to upload to hackage.
* The `upload` mode takes the folder created by prepare and performs the upload to
  hackage.
"""

from subprocess import run, check_call
import shutil
from pathlib import Path
from typing import NamedTuple, Callable, List, Dict, Optional
import tempfile
import re
import pickle
import os


WORK_DIR = Path('.upload-libs')
WORK_DIR.mkdir(exist_ok=True)
OUT_DIR = WORK_DIR / 'docs'
OUT_DIR.mkdir(exist_ok=True)

class Package(NamedTuple):
    name: str
    path: Path
    prepare_sdist: Callable[[], None]

def no_prep():
    pass

def prep_base():
    shutil.copy('config.guess', 'libraries/base')
    shutil.copy('config.sub', 'libraries/base')

def build_copy_file(pkg: Package, f: Path):
    target = Path('_build') / 'stage1' / pkg.path / 'build' / f
    dest = pkg.path / f
    print(f'Building {target} for {dest}...')

    build_cabal = Path('hadrian') / 'build-cabal'
    if not build_cabal.is_file():
        build_cabal = Path('hadrian') / 'build.cabal.sh'

    run([build_cabal, target], check=True)
    dest.parent.mkdir(exist_ok=True, parents=True)
    shutil.copyfile(target, dest)

def modify_file(pkg: Package, fname: Path, f: Callable[[str], str]):
    target = pkg.path / fname
    s = target.read_text()
    target.write_text(f(s))

def prep_ghc_prim():
    build_copy_file(PACKAGES['ghc-prim'], Path('GHC/PrimopWrappers.hs'))

def prep_ghc_bignum():
    shutil.copy('config.guess', 'libraries/base')
    shutil.copy('config.sub', 'libraries/base')

def prep_ghc_boot():
    build_copy_file(PACKAGES['ghc-boot'], Path('GHC/Platform/Host.hs'))
    build_copy_file(PACKAGES['ghc-boot'], Path('GHC/Version.hs'))

def prep_ghc():
    # Drop RTS includes from `include-dirs` as Hackage rejects this
    modify_file(PACKAGES['ghc'], 'ghc.cabal',
                lambda s: s.replace('../rts/dist/build', ''))
    build_copy_file(PACKAGES['ghc'], 'GHC/Platform/Constants.hs')
    build_copy_file(PACKAGES['ghc'], 'GHC/Settings/Config.hs')

PACKAGES = {
    pkg.name: pkg
    for pkg in [
        Package('base', Path("libraries/base"), prep_base),
        Package('ghc-prim', Path("libraries/ghc-prim"), prep_ghc_prim),
        Package('integer-gmp', Path("libraries/integer-gmp"), no_prep),
        Package('ghc-bignum', Path("libraries/ghc-bignum"), prep_ghc_bignum),
        Package('template-haskell', Path("libraries/template-haskell"), no_prep),
        Package('ghc-heap', Path("libraries/ghc-heap"), no_prep),
        Package('ghc-boot', Path("libraries/ghc-boot"), prep_ghc_boot),
        Package('ghc-boot-th', Path("libraries/ghc-boot-th"), no_prep),
        Package('ghc-compact', Path("libraries/ghc-compact"), no_prep),
        Package('libiserv', Path("libraries/libiserv"), no_prep),
        Package('ghc', Path("compiler"), prep_ghc),
    ]
}
# Dict[str, Package]

def cabal_upload(tarball: Path, publish: bool=False, extra_args=[]):
    if publish:
        extra_args += ['--publish']

    run(['cabal', 'upload'] + extra_args + [tarball], check=True)

def prepare_sdist(pkg: Package):

    print(f'Preparing package {pkg.name}...')
    shutil.rmtree(pkg.path / 'dist-newstyle', ignore_errors=True)
    pkg.prepare_sdist()

    # Upload source tarball
    run(['cabal', 'sdist'], cwd=pkg.path, check=True)
    sdist = list((pkg.path / 'dist-newstyle' / 'sdist').glob('*.tar.gz'))[0]
    res_path = shutil.copy(sdist, OUT_DIR)
    return os.path.relpath(res_path, OUT_DIR)

def upload_pkg_sdist(sdist : Path, pkg : Package):
    stamp = WORK_DIR / f'{pkg.name}-sdist'
    if stamp.is_file():
        return
    print(f'Uploading package {pkg.name}...')
    cabal_upload(sdist)

    print()
    print('Check over candidate on Hackage and press enter when ready...')
    input()
    cabal_upload(sdist, publish=True)
    stamp.write_text('')

def get_version(cabal_file: Path) -> Optional[str]:
    m = re.search(r'^version:\s*(\d+(\.\d+)*)', cabal_file.read_text(), re.I | re.M)
    return None if m is None else m.group(1)


def prepare_docs(bindist: Path, pkg: Package):
    """
    Prepare Haddock documentation for a package. bindist
    is the path to an extract binary distribution produced by
    hadrian.
    """
    docdir = bindist / 'docs' / 'html' / 'libraries' / pkg.name
    cabal_file = pkg.path / f'{pkg.name}.cabal'
    version = get_version(cabal_file)
    assert version is not None

    # Build the documentation tarball from the bindist documentation
    stem = f'{pkg.name}-{version}-docs'
    tmp = tempfile.TemporaryDirectory(stem)
    shutil.copytree(docdir, Path(tmp.name) / stem)
    tarball = Path(f'{stem}.tar.gz')
    run(['tar', '-czf', OUT_DIR / tarball, '-H', 'ustar', '-C', tmp.name, stem])
    return tarball

def upload_docs(tarball : Path, pkg : Package):
    stamp = WORK_DIR / f'{pkg.name}-docs'
    if stamp.is_file():
        return
    # Upload the documentation tarball
    print(f'Uploading documentation for {pkg.name}...')
    cabal_upload(tarball, publish=True, extra_args=['--documentation'])
    stamp.write_text('')

def upload_pkg(pkg: Package, d : Path, meta):
    print(f'Uploading {pkg.name}...')
    upload_pkg_sdist(d / meta['sdist'], pkg)
    upload_docs(d / meta['docs'], pkg)

def prepare_pkg(bindist : Path, pkg : Package):
    if pkg.path.exists():
        print(f'Processing {pkg.name}...')
        p1 = prepare_sdist(pkg)
        p2 = prepare_docs(bindist, pkg)
        return { 'sdist' : p1, 'docs': p2 }
    else:
        print(f"Package {pkg.name} doesn't exist... skipping")


def upload_all(bindist: Path):
    for pkg in PACKAGES.values():
        upload_pkg(bindist, pkg)

def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('pkg', type=str, nargs='*', help='package to upload')
    subparsers = parser.add_subparsers(dest="command")

    parser_prepare = subparsers.add_parser('prepare')
    parser_prepare.add_argument('--bindist', required=True, type=Path, help='extracted binary distribution')
    parser_upload = subparsers.add_parser('upload')
    parser_upload.add_argument('--docs', required = True, type=Path, help='folder created by --prepare')
    args = parser.parse_args()

    pkgs = args.pkg
    if pkgs == []:
        pkgs = PACKAGES.keys()

    for pkg_name in pkgs:
        assert pkg_name in PACKAGES


    if args.command == "prepare":
        manifest = {}
        for pkg_name in pkgs:
            print(pkg_name)
            pkg = PACKAGES[pkg_name]
            pkg_meta = prepare_pkg(args.bindist, pkg)
            manifest[pkg] = pkg_meta
        manifest_path = WORK_DIR / 'docs' / 'manifest.pickle'
        with open(WORK_DIR / 'docs' / 'manifest.pickle', 'wb') as fout:
            pickle.dump(manifest, fout)

    elif args.command == "upload":
        manifest_path = args.docs
        with open(manifest_path / 'manifest.pickle', 'rb') as fin:
            manifest = pickle.load(fin)
        for pkg, item in manifest.items():
            print(pkg, item)
            upload_pkg(pkg, manifest_path, item)

if __name__ == '__main__':
    main()

