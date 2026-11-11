#!/usr/bin/env python3
"""Compare every page at an explicit resolution; render changed final pages.

Pixel identity permits reusing a recorded visual inspection of the old page.
Changed pages still require actual visual review. This is not semantic proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import fitz


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('previous', type=Path)
    parser.add_argument('current', type=Path)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--dpi', type=int, default=150)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    previous, current = fitz.open(args.previous), fitz.open(args.current)
    if len(previous) != len(current):
        raise SystemExit('Page count changed: do not reuse page-indexed review.')
    sha = lambda data: hashlib.sha256(data).hexdigest()
    records = []
    for index in range(len(current)):
        before = previous[index].get_pixmap(dpi=args.dpi, alpha=False)
        after = current[index].get_pixmap(dpi=args.dpi, alpha=False)
        b, a = sha(before.samples), sha(after.samples)
        same = (before.width, before.height, b) == (after.width, after.height, a)
        records.append({'page': index + 1, 'previous_pixels_sha256': b,
                        'current_pixels_sha256': a, 'identical': same})
        if not same:
            after.save(args.output_dir / f'page-{index + 1:03}.png')
    report = {'schema': 'ueot.pdf.visual-reuse.v1', 'dpi': args.dpi,
              'previous_pdf_sha256': sha(args.previous.read_bytes()),
              'current_pdf_sha256': sha(args.current.read_bytes()),
              'page_count': len(current),
              'changed_pages': [r['page'] for r in records if not r['identical']],
              'unchanged_pages': [r['page'] for r in records if r['identical']],
              'pages': records,
              'scope': 'Pixel identity only; changed final pages need actual review.'}
    (args.output_dir / 'PIXEL_COMPARISON.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ['pages', 'unchanged_pages']}))


if __name__ == '__main__':
    main()
