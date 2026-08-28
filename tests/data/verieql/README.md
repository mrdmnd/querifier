# VeriEQL LeetCode corpus

This directory contains an unmodified copy of VeriEQL's LeetCode query-pair corpus:

- Source: <https://github.com/VeriEQL/VeriEQL/blob/493cbb81000205e33b0623cfd1c39106fa035fae/benchmarks/leetcode/leetcode.jsonlines>
- Upstream commit: `493cbb81000205e33b0623cfd1c39106fa035fae`
- Git blob: `8f66d312da2155345d7bf019623d1d81a8a56b01`
- SHA-256: `b97fc1293701682a25a2f6345f3630b3482ce49912463a7f4b76ab52665a13c9`
- Size: 22,995,478 bytes
- Records: 23,994 query pairs across 56 LeetCode problem groups

The file is used only by the corpus loader and the opt-in ignored benchmark. The normal semantic regression suite uses a small set of reviewed cases.

Measured bounded coverage, runner configuration, and remaining feature gaps are recorded in [COVERAGE.md](COVERAGE.md).

## License and provenance warning

The upstream repository applies Creative Commons Attribution-NonCommercial-ShareAlike 4.0; the exact license text is in [LICENSE.md](LICENSE.md). The corpus contains SQL submissions attributed upstream to public LeetCode data, but upstream does not provide a dataset-specific rights statement.

Commercial redistribution or use therefore requires an independent rights review and may require permission from the relevant rights holders. The CC BY-NC-SA terms and this notice apply to the imported corpus, not automatically to unrelated querifier source files.

No upstream result file is included. The corpus has no authoritative equivalence label: the first query is a reference and the second is an accepted submission, while upstream `EQU`/`NEQ` files contain verifier outcomes rather than ground truth.
