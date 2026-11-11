-- Edition-local heading policy. The shared book filter remains unchanged.
local notes_seen = {}
local note_number = 0

-- Preserve each complete note once and link subsequent occurrences to it.
-- Markdown keeps all 68 definitions and 78 calls; no note content is omitted.
function Note(note)
  if not FORMAT:match('latex') then return nil end
  local key = pandoc.write(pandoc.Pandoc(note.content), 'native')
  local number = notes_seen[key]
  if number then
    return pandoc.RawInline('latex', '\\textsuperscript{\\hyperlink{ph-note-'
      .. number .. '}{' .. number .. '}}')
  end
  note_number = note_number + 1
  notes_seen[key] = note_number
  local first = note.content[1]
  if first and (first.t == 'Para' or first.t == 'Plain') then
    first.content:insert(1, pandoc.RawInline('latex', '\\hypertarget{ph-note-'
      .. note_number .. '}{}'))
  end
  return note
end

-- Standalone PDFs resolve research links to the exact read-only baseline.
-- Edition-local rights use this review branch; Markdown keeps repository links.
function Link(link)
  if not FORMAT:match('latex') then return nil end
  local target = link.target
  local base = 'https://github.com/MurphyHoops/UEOT/blob/3d443ec29eb17af1fc00699a74e2d42d73516d81/'
  if target:match('^%.%./') then
    link.target = base .. target:sub(4)
  elseif target:match('^source/') then
    link.target = base .. 'philosophy/' .. target
  elseif target == 'PUBLICATION_RIGHTS.md' then
    link.target = 'https://github.com/MurphyHoops/UEOT/blob/pub/philosophy-bilingual-edition/philosophy/PUBLICATION_RIGHTS.md'
  end
  return link
end

function Header(h)
  local title = pandoc.utils.stringify(h.content)
  if h.level == 1 and (title:match('^第.*编') or title:match('^Part [IVX]+')) then
    local label = pandoc.write(pandoc.Pandoc({pandoc.Plain(h.content)}), 'latex'):gsub('%s+$', '')
    local id = h.identifier:gsub('[^%w_.:%-]', '-')
    local prefix, name = label:match('^(Part [IVX]+):%s*(.*)$')
    if not prefix then prefix, name = label:match('^(第.-编)　(.*)$') end
    local display = label
    if prefix then
      display = '{\\Large ' .. prefix .. '}\\\\[1.2em]{\\LARGE '
        .. name .. '}'
    end
    return pandoc.RawBlock('latex', '\\part*{\\phantomsection\\hypertarget{' .. id
      .. '}{}\\addcontentsline{toc}{part}{' .. label .. '}' .. display .. '}')
  end
  if h.level == 2 and (title:match('^第.*章') or title:match('^前言')
      or title:match('^Chapter %d+') or title:match('^Preface')) then
    h.level = 1
  end
  return h
end

function Pandoc(document)
  if not FORMAT:match('latex') then return document end
  -- Keep a chapter's concluding paragraph intact instead of stranding its
  -- final two lines on an otherwise nearly empty continuation page.
  local final_paragraphs = {}
  local in_chapter, last_paragraph = false, nil
  for i, block in ipairs(document.blocks) do
    if block.t == 'Header' or (block.t == 'RawBlock' and block.format == 'latex'
        and block.text:match('^\\part%*')) then
      if in_chapter and last_paragraph then final_paragraphs[last_paragraph] = true end
      local label = block.t == 'Header' and pandoc.utils.stringify(block.content) or ''
      in_chapter = label:match('^第.*章') ~= nil or label:match('^Chapter %d+') ~= nil
      last_paragraph = nil
    elseif in_chapter and block.t == 'Para' then
      last_paragraph = i
    end
  end
  if in_chapter and last_paragraph then final_paragraphs[last_paragraph] = true end
  local blocks = pandoc.List({pandoc.RawBlock('latex', '\\begingroup\\small\\setlength{\\parskip}{0.25em}')})
  local in_colophon = true
  local in_bibliography = false
  for i, block in ipairs(document.blocks) do
    if block.t == 'Header' and block.identifier == 'ph-c-1' then
      -- Reserve room for the section heading, repeated table header and first
      -- row; otherwise a longtable may strand its heading on the prior page.
      blocks:insert(pandoc.RawBlock('latex', '\\par\\ifdim\\dimexpr\\pagegoal-\\pagetotal\\relax<12\\baselineskip\\newpage\\fi'))
    end
    if in_colophon and block.t == 'Header' then
      local label = pandoc.utils.stringify(block.content)
      if label:match('^前言') or label:match('^Preface') then
        blocks:insert(pandoc.RawBlock('latex', '\\par\\endgroup'))
        in_colophon = false
      end
    end
    if final_paragraphs[i] then
      blocks:insert(pandoc.RawBlock('latex', '\\begingroup\\interlinepenalty=10000'))
    end
    blocks:insert(block)
    if final_paragraphs[i] then
      blocks:insert(pandoc.RawBlock('latex', '\\par\\endgroup'))
    end
    if block.t == 'Header' and block.identifier == 'ph-d-3' then
      blocks:insert(pandoc.RawBlock('latex', '\\begingroup\\small\\raggedright\\setlength{\\parskip}{0.25em}'))
      in_bibliography = true
    end
  end
  if in_colophon then blocks:insert(pandoc.RawBlock('latex', '\\par\\endgroup')) end
  if in_bibliography then blocks:insert(pandoc.RawBlock('latex', '\\par\\endgroup')) end
  document.blocks = blocks
  return document
end
