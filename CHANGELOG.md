# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- next-header -->

## [Unreleased] - ReleaseDate

### Added

* Implement `CompactEncoding` for:
  - `SocketAddrV4`
  - `SocketAddrV6`
  - `Ipv4Addr`
  - `Ipv6Addr`
* We also implement `CompactEncoding` for `usize` as a variable width integer.
  The same as the JavaScript "uint" encoding

### Changed

### Removed


<!-- next-url -->
[Unreleased]: https://github.com/datrs/compact-encoding/compare/v2.0.0...HEAD
