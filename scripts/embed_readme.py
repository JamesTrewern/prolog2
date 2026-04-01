#!/usr/bin/env python3
"""
Embeds file contents into README.md files using sentinel comments.

Usage:
    python3 scripts/embed_readme.py [examples_dir]

Sentinel format in README.md:
    <!-- embed-start: filename.ext -->
    ```lang
    ...content replaced automatically...
    ```
    <!-- embed-end: filename.ext -->

File paths in sentinels are relative to the README's directory.
Language for the code block is inferred from the file extension.
Subdirectories of examples_dir without a README.md are silently skipped.
"""

import re
import sys
from pathlib import Path

LANG_MAP = {
    '.json': 'json',
    '.pl': 'prolog',
    '.py': 'python',
    '.js': 'javascript',
    '.ts': 'typescript',
    '.sh': 'bash',
}

EMBED_PATTERN = re.compile(
    r'(<!-- embed-start: (?P<filename>[^\s>]+) -->)'
    r'.*?'
    r'(<!-- embed-end: (?P=filename) -->)',
    re.DOTALL,
)


def get_language(filename: str) -> str:
    return LANG_MAP.get(Path(filename).suffix, '')


def embed_files_in_readme(readme_path: Path) -> bool:
    content = readme_path.read_text()

    def replace(match):
        filename = match.group('filename')
        start_marker = match.group(1)
        end_marker = match.group(3)

        file_path = readme_path.parent / filename
        if not file_path.exists():
            print(f"  Warning: {file_path} not found, skipping", file=sys.stderr)
            return match.group(0)

        lang = get_language(filename)
        file_content = file_path.read_text().rstrip()
        return f"{start_marker}\n```{lang}\n{file_content}\n```\n{end_marker}"

    new_content = EMBED_PATTERN.sub(replace, content)

    if new_content != content:
        readme_path.write_text(new_content)
        return True
    return False


def main():
    examples_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('examples')

    if not examples_dir.is_dir():
        print(f"Error: '{examples_dir}' is not a directory", file=sys.stderr)
        sys.exit(1)

    changed = []
    for subdir in sorted(examples_dir.iterdir()):
        if not subdir.is_dir():
            continue
        readme = subdir / 'README.md'
        if not readme.exists():
            continue
        if embed_files_in_readme(readme):
            changed.append(str(readme))
            print(f"Updated: {readme}")

    if changed:
        print(f"\n{len(changed)} README(s) updated.")


if __name__ == '__main__':
    main()
