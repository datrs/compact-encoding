# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- next-header -->

## [Unreleased] - ReleaseDate

### Added

* Implement `CompactEncoding<Vec<u8>>` for `&[u8]`, allowing byte slices to be encoded directly
* Implement `CompactEncoding<Vec<D>>` for `&[T]` where `T: VecEncodable<D>`, enabling encoding of slices like `&[&[u8]]`
* Implement `VecEncodable` for `Vec<u8>` to support `Vec<Vec<u8>>`
* Implement `VecEncodable<Vec<u8>>` for `&[u8]` to support `&[&[u8]]`

### Changed

* `VecEncodable` trait now has an optional `Decode` type parameter (defaults to `Self`) to support types where the encoded type differs from the decoded type

### Removed



## [2.1.0] - 2025-12-09

### Added

### Changed

### Removed



## [2.1.0] - 2025-12-09

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
[Unreleased]: https://github.com/datrs/compact-encoding/compare/v2.1.0...HEAD
[2.1.0]: https://github.com/datrs/compact-encoding/compare/v2.1.0...v2.1.0
[2.1.0]: https://github.com/datrs/compact-encoding/compare/v2.0.0...v2.1.0
