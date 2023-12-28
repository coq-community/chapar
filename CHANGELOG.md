# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Fixed
- Build with Coq 8.19 and beyond

## [8.16.0] - 2023-10-01

### Changed
- Adjust build for Coq 8.18 and beyond
- Use Dune wrapping for OCaml modules
- Remove boilerplate for OCamlbuild
- Move bash scripts to scripts directory
- Use standard theories/src directory names

### Fixed
- Stores build with Dune 3.6 or later
- Nix CI configuration
- List lemma deprecations in 8.18

## [8.15.0] - 2023-02-05
### Changed
- Removed unecessary imports
- Adjust build for Coq 8.16 and beyond

### Fixed
- Deprecations related to Stdlib Nat module

## [8.14.0] - 2022-01-12
### Changed
- Add hint locality everywhere and consequently require Coq 8.14 or later

### Fixed
- Use consistent conventions for `Require Import`

## [8.13.0] - 2021-08-02
### Changed
- Make most hints local
- Adjust build for Coq 8.13 and beyond

## [8.12.0] - 2020-10-01
### Changed
- OCaml OPAM package definition uses Dune
- Reorganize extraction to support Dune
- Coq OPAM package definition uses Dune
- Declare all scopes and consequently require Coq 8.10 or later

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

[Unreleased]: https://github.com/coq-community/chapar/compare/v8.16.0...master
[8.16.0]: https://github.com/coq-community/chapar/releases/tag/v8.16.0
[8.15.0]: https://github.com/coq-community/chapar/releases/tag/v8.15.0
[8.14.0]: https://github.com/coq-community/chapar/releases/tag/v8.14.0
[8.13.0]: https://github.com/coq-community/chapar/releases/tag/v8.13.0
[8.12.0]: https://github.com/coq-community/chapar/releases/tag/v8.12.0
[8.11.0]: https://github.com/coq-community/chapar/releases/tag/v8.11.0
[8.10.0]: https://github.com/coq-community/chapar/releases/tag/v8.10.0
[8.9.0]: https://github.com/coq-community/chapar/releases/tag/v8.9.0
