-- Mathematics-only print filter. Based on tools/books/print.lua.
-- Explicit labels make inline theorem anchors work with Pandoc hyperref links.
-- Permit long Lean names and file paths to wrap without changing the Markdown.
function Code(element)
  if FORMAT:match('latex') and #element.text > 12
      and not element.text:find('[{}\\]') then
    return pandoc.RawInline('latex', '\\nolinkurl{' .. element.text .. '}')
  end
end

-- A proof-end mark belongs to the mathematical symbol font, including when
-- the editable Markdown uses the literal Unicode character in ordinary text.
function Math(element)
  -- The translated mode-of-convergence clause in 39.22 is longer than the
  -- Chinese label. Keep its exact tokens and put the clause on a second line.
  local label = "\\quad\\text{in the original source's }"
  if FORMAT:match('latex') and element.mathtype == 'DisplayMath'
      and element.text:find(label, 1, true) then
    local first, last = element.text:find(label, 1, true)
    element.text = '\\begin{gathered}' .. element.text:sub(1, first - 1)
      .. '\\\\' .. element.text:sub(first + 5) .. '\\end{gathered}'
    return element
  end
end

function Str(element)
  if not FORMAT:match('latex') then return nil end
  local result = pandoc.List()
  local changed = false
  local function plain(text)
    local rest = text
    while rest:find('∎', 1, true) do
      local first, last = rest:find('∎', 1, true)
      if first > 1 then result:insert(pandoc.Str(rest:sub(1, first - 1))) end
      result:insert(pandoc.Math('InlineMath', '\\blacksquare'))
      rest = rest:sub(last + 1)
      changed = true
    end
    if #rest > 0 then result:insert(pandoc.Str(rest)) end
  end
  -- Source prose also contains unquoted FQNs and full SHA-256 values. Break
  -- those literal ASCII tokens at legal URL breaks; never shorten their bytes.
  local cursor = 1
  for first, token, after in element.text:gmatch('()([A-Za-z0-9][A-Za-z0-9_./%-]*)()') do
    if #token > 24 or (#token > 12 and
        (token:find('[a-z][A-Z]') or token:find('[_/]'))) then
      plain(element.text:sub(cursor, first - 1))
      result:insert(pandoc.RawInline('latex', '\\nolinkurl{' .. token .. '}'))
      cursor = after
      changed = true
    end
  end
  plain(element.text:sub(cursor))
  if changed then return result end
end

function Pandoc(document)
  if not FORMAT:match('latex') then return document end
  local philosophy = pandoc.utils.stringify(document.meta['ueot-book']) == 'philosophy'
  local blocks = pandoc.List()
  local anchor = nil
  for _, block in ipairs(document.blocks) do
    local id = nil
    if block.t == 'RawBlock' and block.format == 'html' then
      id = block.text:match('^%s*<a id="([%w_.:%-]+)"></a>%s*$')
    elseif block.t == 'Para' and #block.content == 2 then
      -- Pandoc 3.1 parses a standalone <a id="..."></a> as two raw
      -- inlines in a paragraph. Preserve its target just like a raw block.
      local first, last = block.content[1], block.content[2]
      if first.t == 'RawInline' and first.format == 'html'
          and last.t == 'RawInline' and last.format == 'html'
          and last.text == '</a>' then
        id = first.text:match('^<a id="([%w_.:%-]+)">$')
      end
    end
    if id then
      anchor = id
    else
      if anchor then
        if block.t == 'Header' then
          block.identifier = anchor
        else
          blocks:insert(pandoc.RawBlock('latex', '\\hypertarget{' .. anchor .. '}{}\\phantomsection\\label{' .. anchor .. '}'))
        end
        anchor = nil
      end
      -- The endpoint table follows immediately; keep its heading off the
      -- otherwise empty bottom of the previous printed page.
      if block.t == 'Header' and block.level == 3
          and (pandoc.utils.stringify(block.content) == '21.7.6 Endpoints and invalid inferences'
            or pandoc.utils.stringify(block.content) == '21.7.6 端点与不成立的推论') then
        blocks:insert(pandoc.RawBlock('latex', '\\pagebreak'))
      end
      -- Keep the long Chinese Appendix D title from leaving one final
      -- character alone. The optional title preserves the unchanged TOC
      -- and PDF bookmark; this is solely a print-layout line break.
      if block.t == 'Header' and block.level == 1
          and pandoc.utils.stringify(block.content) == '附录 D. v3.0 完整可执行验证与历史输出' then
        blocks:insert(pandoc.RawBlock('latex',
          '\\chapter[附录 D. v3.0 完整可执行验证与历史输出]'
          .. '{附录 D. v3.0\\\\完整可执行验证与历史输出}'
          .. '\\label{' .. block.identifier .. '}'))
      elseif philosophy and block.t == 'Header' then
        local label = pandoc.utils.stringify(block.content)
        if block.level == 1 and label:match('^第.*编') then
          blocks:insert(pandoc.RawBlock('latex', '\\part*{\\phantomsection'
            .. '\\addcontentsline{toc}{part}{' .. label .. '}' .. label .. '}'))
        else
          if block.level == 2 and (label:match('^第.*章') or label:match('^前言')) then
            block.level = 1
          end
          blocks:insert(block)
        end
      else
        blocks:insert(block)
      end
    end
  end
  document.blocks = blocks
  return document
end
