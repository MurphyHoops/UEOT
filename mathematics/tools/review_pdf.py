#!/usr/bin/env python3
"""Inspect every PDF page and optionally render contact sheets for visual review.
The JSON is mechanical evidence, not a substitute for actually viewing the pages.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess
import fitz
from PIL import Image,ImageDraw

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('pdf',type=Path);ap.add_argument('--output-dir',type=Path,required=True)
 ap.add_argument('--render',action='store_true');a=ap.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
 d=fitz.open(a.pdf);pages=[];bad_links=[];ninternal=0;fonts=set()
 for i,p in enumerate(d):
  spans=[s for b in p.get_text('dict')['blocks'] if 'lines' in b for l in b['lines'] for s in l['spans'] if s['text'].strip()]
  outside=[{'text':s['text'],'bbox':s['bbox']} for s in spans if s['bbox'][0]<-0.5 or s['bbox'][1]<-0.5 or s['bbox'][2]>p.rect.width+0.5 or s['bbox'][3]>p.rect.height+0.5]
  margin=[{'text':s['text'],'bbox':s['bbox']} for s in spans if (s['bbox'][0]<66 or s['bbox'][2]>p.rect.width-66) and 60<s['bbox'][1]<780]
  for x in p.get_fonts():fonts.add(x[0])
  for x in p.get_links():
   if x['kind'] in [fitz.LINK_GOTO,fitz.LINK_NAMED] and ('page' in x or 'nameddest' in x):
    ninternal+=1
    if not(0<=x.get('page',-1)<len(d)):bad_links.append({'page':i+1,'link':str(x)})
  text=p.get_text()
  pages.append({'page':i+1,'width':p.rect.width,'height':p.rect.height,'text_length':len(text),'outside_page':outside,'margin_candidates':margin,'replacement_character': '\ufffd' in text})
  if a.render:
   img=p.get_pixmap(matrix=fitz.Matrix(.6,.6),alpha=False)
   img.save(a.output_dir/f'page-{i+1:03}.png')
 contacts=[]
 if a.render:
  for first in range(0,len(d),12):
   thumbw,thumbh=358,506;sheet=Image.new('RGB',(4*(thumbw+12)+12,3*(thumbh+32)+12),'#dddddd');draw=ImageDraw.Draw(sheet)
   for j in range(min(12,len(d)-first)):
    im=Image.open(a.output_dir/f'page-{first+j+1:03}.png');im.thumbnail((thumbw,thumbh))
    x=12+(j%4)*(thumbw+12);y=28+(j//4)*(thumbh+32)
    draw.text((x,y-18),f'{a.pdf.stem} | PDF page {first+j+1}',fill='black');sheet.paste(im,(x,y))
   name=f'contact-{first+1:03}-{min(first+12,len(d)):03}.png';sheet.save(a.output_dir/name);contacts.append(name)
 names=d.resolve_names();pids=sorted(x for x in names if x.startswith('p-'))
 fontinfo=[]
 for x in sorted(fonts):
  name,ext,typ,data=d.extract_font(x);fontinfo.append({'xref':x,'name':name,'format':ext,'type':typ,'embedded_bytes':len(data)})
 report={'schema':'ueot.pdf.mechanical.v1','pdf':str(a.pdf),'sha256':hashlib.sha256(a.pdf.read_bytes()).hexdigest(),'page_count':len(d),'toc_count':len(d.get_toc()),'internal_links':ninternal,'unresolved_internal_links':bad_links,'named_P_targets':len(pids),'P_targets':pids,'fonts':fontinfo,'all_fonts_embedded':all(x['embedded_bytes']>0 for x in fontinfo),'outside_page_count':sum(len(x['outside_page']) for x in pages),'replacement_character_pages':[x['page'] for x in pages if x['replacement_character']],'margin_candidate_pages':[x['page'] for x in pages if x['margin_candidates']],'contact_sheets':contacts,'pages':pages,'scope':'All-page mechanical inspection and actual render; visual acceptance requires a separate reviewer record.'}
 (a.output_dir/'PDF_MECHANICAL.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
 (a.output_dir/'pdffonts.txt').write_text(subprocess.check_output(['pdffonts',str(a.pdf)],text=True))
 print(json.dumps({k:v for k,v in report.items() if k not in ['pages','fonts','P_targets','contact_sheets']},ensure_ascii=False))
if __name__=='__main__':main()
