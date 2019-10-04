# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]
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

[Unreleased]: https://github.com/coq-community/chapar/compare/v8.9.0...master
[8.9.0]: https://github.com/coq-community/chapar/releases/tag/v8.9.0
