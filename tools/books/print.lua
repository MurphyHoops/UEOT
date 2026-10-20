-- Permit long Lean names and file paths to wrap without changing the Markdown.
function Code(element)
  if FORMAT:match('latex') and #element.text > 24
      and not element.text:find('[{}\\]') then
    return pandoc.RawInline('latex', '\\nolinkurl{' .. element.text .. '}')
  end
end

-- A proof-end mark belongs to the mathematical symbol font, including when
-- the editable Markdown uses the literal Unicode character in ordinary text.
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
    if #token > 24 then
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
    end
    if id then
      anchor = id
    else
      if anchor then
        if block.t == 'Header' then
          block.identifier = anchor
        else
          blocks:insert(pandoc.RawBlock('latex', '\\hypertarget{' .. anchor .. '}{}'))
        end
        anchor = nil
      end
      if philosophy and block.t == 'Header' then
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
