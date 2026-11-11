#!/usr/bin/env python3
"""Render whole-book overview sheets and selected full pages for actual visual review.

This produces render/geometry evidence, not an assertion that a reviewer viewed it.
Requires PyMuPDF and Pillow. Page numbers in this tool are one-based PDF pages.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

import fitz
from PIL import Image, ImageDraw, ImageFont


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--pages', default='1')
    args = parser.parse_args()
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    doc = fitz.open(args.pdf)
    font = ImageFont.truetype('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf', 14)
    page_data, thumbs = [], []
    for index, page in enumerate(doc):
        pix = page.get_pixmap(matrix=fitz.Matrix(.32, .32), alpha=False)
        thumbs.append(Image.frombytes('RGB', [pix.width, pix.height], pix.samples))
        spans = [s for b in page.get_text('dict')['blocks'] if 'lines' in b
                 for line in b['lines'] for s in line['spans'] if s['text'].strip()]
        beyond = [s['text'][:100] for s in spans
                  if not (page.rect + (-2, -2, 2, 2)).contains(fitz.Rect(s['bbox']))]
        links = page.get_links()
        page_data.append({'page': index+1, 'text_characters': len(page.get_text()),
                          'text_span_count': len(spans), 'text_outside_page': beyond,
                          'links': len(links),
                          'invalid_internal_links': [l for l in links
                              if l.get('kind') == fitz.LINK_GOTO and
                              not 0 <= l.get('page', -1) < len(doc)]})
    sheets = []
    w, h = 208, 296
    for start in range(0, len(doc), 36):
        sheet = Image.new('RGB', (6*w, 6*h), '#e4e7ea')
        draw = ImageDraw.Draw(sheet)
        for offset, thumb in enumerate(thumbs[start:start+36]):
            x, y = (offset % 6)*w, (offset // 6)*h
            sheet.paste(thumb, (x+(w-thumb.width)//2, y+22))
            draw.text((x+8, y+3), f'PDF {start+offset+1}', fill='#202b32', font=font)
        path = out / f'overview-{start+1:03d}-{min(start+36,len(doc)):03d}.png'
        sheet.save(path)
        sheets.append({'file': path.name, 'first_page': start+1,
                       'last_page': min(start+36,len(doc)), 'sha256': sha(path)})
    selected = []
    for num in sorted(set(int(x) for x in args.pages.split(',') if x)):
        if not 1 <= num <= len(doc):
            raise ValueError(f'Page {num} is out of range')
        path = out / f'page-{num:03d}.png'
        doc[num-1].get_pixmap(dpi=110, alpha=False).save(path)
        selected.append({'page': num, 'file': path.name, 'sha256': sha(path), 'dpi': 110})
    result = {'schema': 'ueot_physics.pdf_render.v1',
              'created_at_utc': datetime.now(timezone.utc).isoformat(),
              'pdf_name': args.pdf.name, 'pdf_sha256': sha(args.pdf),
              'page_count': len(doc), 'outline': doc.get_toc(),
              'overview_sheets': sheets, 'selected_full_pages': selected,
              'page_geometry': page_data,
              'review_status': 'RENDERED_REQUIRES_ACTUAL_VISUAL_INSPECTION',
              'scope': 'Rendering and geometric inspection cannot establish mathematical correctness or full-page reading.'}
    (out/'render.json').write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print(json.dumps({'pages': len(doc), 'overview_sheets': len(sheets),
                      'full_pages_rendered': len(selected),
                      'text_outside_page': sum(bool(x['text_outside_page']) for x in page_data),
                      'invalid_internal_links': sum(len(x['invalid_internal_links']) for x in page_data),
                      'receipt': str(out/'render.json')}, ensure_ascii=False))


if __name__ == '__main__':
    main()
