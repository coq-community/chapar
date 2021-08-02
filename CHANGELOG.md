# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]
### Changed
- OCaml OPAM package definition uses Dune
- Reorganize extraction to support Dune
- Coq OPAM package definition uses Dune
- Declare all scopes and consequently require Coq 8.10 or later
- Make most hints local

### Added
- Support for OCaml builds with Dune
- Support for Coq builds with Dune

### Fixed
- Remove dependency on a local functional extensionality axiom

### Removed
- All uses of UTF-8

## [8.11.0] - 2020-01-31
### Fixed
- Compatibility with Coq 8.11
- Ignore more untracked files such as `.vos`
- Remove mention of extracted OPAM package in README.md

### Changed
- Add `Proof using` annotations for faster `.vos`/`.vio` compilation
- Ignore undeclared scope warnings

## [8.10.0] - 2019-10-14
### Removed
- Unused library lemmas and functions originally from a formalization of separation logic that were vendored

### Fixed
- Hint and declaration deprecation warnings
- Switch from deprecated `omega` tactic to `lia`

### Changed
- Use LF newlines everywhere, in place of CRLF

## [8.9.0] - 2019-05-15
### Fixed
- Support for Coq 8.9 and later (port from Coq 8.4)
- OCaml compilation of extracted code (OCaml 4.05.0 or later and Batteries 2.8.0 or later)

### Changed
- Modernize build scripts to use `coq_makefile` features
- Reorganize code into subdirectories

[Unreleased]: https://github.com/coq-community/chapar/compare/v8.11.0...master
[8.11.0]: https://github.com/coq-community/chapar/releases/tag/v8.11.0
[8.10.0]: https://github.com/coq-community/chapar/releases/tag/v8.10.0
[8.9.0]: https://github.com/coq-community/chapar/releases/tag/v8.9.0
