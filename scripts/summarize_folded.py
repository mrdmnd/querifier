from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Iterable
from pathlib import Path

FrameCounts = Counter[str]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Summarize inclusive and self samples from folded stacks."
    )
    parser.add_argument("path", type=Path, help="Folded stack file")
    parser.add_argument("--limit", type=int, default=25, help="Rows per section")
    return parser.parse_args()


def read_stacks(path: Path) -> Iterable[tuple[list[str], int]]:
    with path.open(encoding="utf-8") as folded:
        for line_number, raw_line in enumerate(folded, start=1):
            stack, separator, raw_count = raw_line.rstrip().rpartition(" ")
            if not separator or not stack:
                raise ValueError(f"{path}:{line_number}: malformed folded stack")
            try:
                count = int(raw_count)
            except ValueError as error:
                raise ValueError(
                    f"{path}:{line_number}: invalid sample count {raw_count!r}"
                ) from error
            yield stack.split(";"), count


def simplify(frame: str) -> str:
    _, separator, symbol = frame.partition("`")
    return symbol if separator else frame


def print_rows(
    heading: str,
    rows: Iterable[tuple[str, int]],
    total: int,
    limit: int,
) -> None:
    print(heading)
    for frame, samples in list(rows)[:limit]:
        percentage = samples * 100.0 / total
        print(f"{samples}\t{percentage:.2f}%\t{simplify(frame)}")


def main() -> None:
    args = parse_args()
    if args.limit <= 0:
        raise ValueError("--limit must be greater than zero")

    inclusive: FrameCounts = Counter()
    self_samples: FrameCounts = Counter()
    total = 0
    for frames, samples in read_stacks(args.path):
        total += samples
        self_samples[frames[-1]] += samples
        for frame in dict.fromkeys(frames):
            inclusive[frame] += samples

    print(f"total_samples\t{total}")
    print_rows("top_self", self_samples.most_common(), total, args.limit)
    print_rows(
        "top_querifier_inclusive",
        (
            item
            for item in inclusive.most_common()
            if "querifier::" in item[0]
        ),
        total,
        args.limit,
    )
    print_rows(
        "top_z3_api_inclusive",
        (
            item
            for item in inclusive.most_common()
            if "`Z3_" in item[0] or "`<z3::" in item[0]
        ),
        total,
        args.limit,
    )


if __name__ == "__main__":
    main()
