#!/usr/bin/env python3
"""Reject proof admissions and non-strict proof modes in local EasyCrypt sources."""
from pathlib import Path
import re
import sys


def without_comments(text):
    # EasyCrypt comments nest. Preserve strings, including pragma names, and
    # preserve line breaks so diagnostics refer to the original source.
    tokens = re.compile(r'\(\*|\*\)|"(?:\\.|[^"\\])*"', re.DOTALL)
    result = []
    depth = 0
    start = 0
    for match in tokens.finditer(text):
        chunk = text[start:match.start()]
        result.append(re.sub(r"[^\n]", " ", chunk) if depth else chunk)
        token = match.group()
        if token == "(*":
            depth += 1
            result.append("  ")
        elif token == "*)" and depth:
            depth -= 1
            result.append("  ")
        else:
            result.append(re.sub(r"[^\n]", " ", token) if depth else token)
        start = match.end()
    chunk = text[start:]
    result.append(re.sub(r"[^\n]", " ", chunk) if depth else chunk)
    if depth:
        raise ValueError("unterminated comment")
    return "".join(result)


def main():
    root = Path(__file__).resolve().parent.parent
    files = ([Path(arg) for arg in sys.argv[1:]] if len(sys.argv) > 1 else
             sorted([*root.glob("*.ec"), *root.glob("*.eca"),
                     *root.glob("tests/*.ec")]))
    failed = False
    for path in files:
        try:
            source = without_comments(path.read_text())
        except ValueError as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
            continue
        for match in re.finditer(r"\b(?:admit|admitted)\b|Proofs:(?:weak|report)", source):
            line = source.count("\n", 0, match.start()) + 1
            print(f"{path}:{line}: forbidden proof bypass: {match.group()}", file=sys.stderr)
            failed = True
    if failed:
        return 1
    print(f"Proof policy checked: {len(files)} local files, no admissions or weak proof modes.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
