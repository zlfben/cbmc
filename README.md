[![Build Status][travis_img]][travis]
[![Build Status][codebuild_img]][codebuild]
[![Build Status][codebuild_windows_img]][codebuild_windows]
[![Build Status][coverity_img]][coverity]
[![Build Status][codecov_img]][codecov]

[CProver Wiki](http://www.cprover.org/wiki)

[CProver Documentation](http://cprover.diffblue.com)

About
=====

CBMC is a Bounded Model Checker for C and C++ programs. It supports C89, C99,
most of C11 and most compiler extensions provided by gcc and Visual Studio. It
also supports SystemC using Scoot. It allows verifying array bounds (buffer
overflows), pointer safety, exceptions and user-specified assertions.
Furthermore, it can check C and C++ for consistency with other languages, such
as Verilog. The verification is performed by unwinding the loops in the program
and passing the resulting equation to a decision procedure.

For full information see [cprover.org](http://www.cprover.org/cbmc).

Versions
========

Get the [latest release](https://github.com/diffblue/cbmc/releases)
* Releases are tested and for production use.

Get the current *develop* version: `git clone https://github.com/diffblue/cbmc.git`
* Develop versions are not recommended for production use.

Installing
==========

### Windows

For windows you can install cbmc binaries via the .msi's found on the
[releases](https://github.com/diffblue/cbmc/releases) page.

Note that we depend on the Visual C++ redistributables. You likely
already have these, if not please download and run vcredist.x64.exe from
[Microsoft](https://support.microsoft.com/en-gb/help/2977003/the-latest-supported-visual-c-downloads) to install them prior to running
cbmc.

### macOS

For macOS there is a [Homebrew](https://brew.sh) package
[available](https://formulae.brew.sh/formula/cbmc). Once you have installed
Homebrew, simply run

    brew install cbmc

to install cbmc, or if you already have it installed via homebrew

    brew upgrade cbmc

to get an up-to-date version.

Report bugs
===========

If you encounter a problem please file a bug report:
* Create an [issue](https://github.com/diffblue/cbmc/issues)

Contributing to the code base
=============================

1. Fork the repository
2. Clone the repository `git clone git@github.com:YOURNAME/cbmc.git`
3. Create a branch from the `develop` branch (default branch)
4. Make your changes (follow the [coding guidelines](https://github.com/diffblue/cbmc/blob/develop/CODING_STANDARD.md))
5. Push your changes to your branch
6. Create a Pull Request targeting the `develop` branch

New contributors can look through the [mini
projects](https://github.com/diffblue/cbmc/blob/develop/MINI-PROJECTS.md)
page for small, focussed feature ideas.

License
=======
4-clause BSD license, see `LICENSE` file.

[travis]: https://travis-ci.org/diffblue/cbmc
[travis_img]: https://travis-ci.org/diffblue/cbmc.svg?branch=master
[codebuild]: https://us-east-1.console.aws.amazon.com/codesuite/codebuild/projects/cbmc/history?region=us-east-1
[codebuild_img]: https://codebuild.us-east-1.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiajhxcmNGUEgyV0xZa2ZFaVd3czJmbm1DdEt3QVdJRVdZaGJuMTUwOHFrZUM3eERwS1g4VEQ3Ymw3bmFncldVQXArajlYL1pXbGZNVTdXdndzUHU4Ly9JPSIsIml2UGFyYW1ldGVyU3BlYyI6IkVUUEdWVEt0SUFONlhyNVAiLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=develop
[codebuild_windows]: https://us-east-1.console.aws.amazon.com/codesuite/codebuild/projects/cbmc-windows/history?region=us-east-1
[codebuild_windows_img]: https://codebuild.us-east-1.amazonaws.com/badges?uuid=eyJlbmNyeXB0ZWREYXRhIjoiTFQ4Q0lCSEc1Rk5NcmlzaFZDdU44Vk8zY0c1VCtIVWMwWnJMRitmVFI5bE94Q3dhekVPMWRobFU2Q0xTTlpDSWZUQ3J1eksrWW1rSll1OExXdll2bExZPSIsIml2UGFyYW1ldGVyU3BlYyI6InpqcloyaEdxbjBiQUtvNysiLCJtYXRlcmlhbFNldFNlcmlhbCI6MX0%3D&branch=develop
[coverity]: https://scan.coverity.com/projects/diffblue-cbmc
[coverity_img]: https://scan.coverity.com/projects/13552/badge.svg
[codecov]: https://codecov.io/gh/diffblue/cbmc
[codecov_img]: https://codecov.io/gh/diffblue/cbmc/branch/develop/graphs/badge.svg
