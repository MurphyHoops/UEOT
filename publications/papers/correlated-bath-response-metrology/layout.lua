-- Publication typography and float layout filter for Physical Review A / master XeLaTeX build.
-- 1. Suppresses redundant Markdown horizontal rules (---) between sections/appendices.
-- 2. Sanitizes math in headings for clean Unicode PDF bookmarks (\mathbb{R} \times S^1 -> R x S^1).
-- 3. Converts `.theorem` and `.remark` fenced Divs into formal amsthm environments.
-- 4. Converts Markdown tables (with native Pandoc `: Caption {#tab:...}`) into floating APS tables.

local function clean_bookmark(s)
  s = s:gsub("\xc2\xa0", " ")
  s = s:gsub("\\mathbb%s*{R}", "ℝ")
  s = s:gsub("\\times", "×")
  s = s:gsub("S%^1", "S¹")
  s = s:gsub("S%^{1}", "S¹")
  s = s:gsub("%$", "")
  s = s:gsub("[ \t\r\n]+", " ")
  return (s:gsub("^[ \t\r\n]+", ""):gsub("[ \t\r\n]+$", ""))
end

function HorizontalRule()
  if FORMAT:match("latex") then
    return {}
  end
end

function Math(m)
  if FORMAT:match("latex") then
    m.text = m.text:gsub("–", "--")
    return m
  end
end

function Header(el)
  if not FORMAT:match("latex") then
    return el
  end
  local has_math = false
  for _, inl in ipairs(el.content) do
    if inl.t == "Math" then
      has_math = true
      break
    end
  end
  local tex_body = pandoc.write(pandoc.Pandoc({pandoc.Plain(el.content)}), "latex"):gsub("%s+$", "")
  if has_math then
    local plain_text = clean_bookmark(pandoc.utils.stringify(el.content))
    local cmd = (el.level == 1) and "\\section" or ((el.level == 2) and "\\subsection" or "\\subsubsection")
    local label_str = (el.identifier ~= "") and ("\\label{" .. el.identifier .. "}") or ""
    return pandoc.RawBlock("latex", cmd .. "{\\texorpdfstring{" .. tex_body .. "}{" .. plain_text .. "}}" .. label_str)
  end
  return el
end

function Div(el)
  if not FORMAT:match("latex") then
    return el
  end
  local is_thm = el.classes:includes("theorem")
  local is_rem = el.classes:includes("remark")
  if not (is_thm or is_rem) then
    return el
  end
  local env = is_thm and "theorem" or "remark"
  local title = el.attributes["title"]
  local opt = (title and title ~= "") and ("[" .. title .. "]") or ""
  local label_str = (el.identifier ~= "") and ("\\label{" .. el.identifier .. "}") or ""
  local prefix = "\\Needspace{6\\baselineskip}\\begin{" .. env .. "}" .. opt .. label_str
  local blocks = {pandoc.RawBlock("latex", prefix)}
  for _, blk in ipairs(el.content) do
    table.insert(blocks, blk)
  end
  table.insert(blocks, pandoc.RawBlock("latex", "\\end{" .. env .. "}"))
  return blocks
end

local function blocks_to_latex(blocks)
  local converted = pandoc.walk_block(pandoc.Div(blocks), {
    Cite = function(c)
      local keys = {}
      for _, cit in ipairs(c.citations) do
        table.insert(keys, cit.id)
      end
      return pandoc.RawInline("latex", "\\citep{" .. table.concat(keys, ",") .. "}")
    end
  }).content
  local s = pandoc.write(pandoc.Pandoc(converted), "latex")
  return (s:gsub("%s+$", ""):gsub("^%s+", ""))
end

local function inlines_to_latex(inlines)
  local s = pandoc.write(pandoc.Pandoc({pandoc.Plain(inlines)}), "latex")
  return (s:gsub("%s+$", ""):gsub("^%s+", ""))
end

local function col_spec_for(tbl)
  local ncols = #tbl.colspecs
  local head_txt = ""
  if tbl.head and #tbl.head.rows > 0 then
    head_txt = pandoc.utils.stringify(tbl.head.rows[1].cells[1].contents)
  end
  if ncols == 4 and head_txt:match("Protocol") then
    return ">{\\raggedright\\arraybackslash}p{0.22\\linewidth} >{\\raggedright\\arraybackslash}p{0.23\\linewidth} >{\\raggedright\\arraybackslash}X >{\\raggedright\\arraybackslash}p{0.22\\linewidth}"
  elseif ncols == 5 then
    return ">{\\raggedright\\arraybackslash}p{0.23\\linewidth} r r >{\\raggedright\\arraybackslash}p{0.31\\linewidth} >{\\raggedright\\arraybackslash}X"
  elseif ncols == 4 and head_txt:match("Probe") then
    return ">{\\raggedright\\arraybackslash}p{0.22\\linewidth} c c >{\\raggedright\\arraybackslash}X"
  end
  local specs = {}
  for i = 1, ncols do
    table.insert(specs, (i == 1) and ">{\\raggedright\\arraybackslash}p{0.24\\linewidth}" or ">{\\raggedright\\arraybackslash}X")
  end
  return table.concat(specs, " ")
end

local function render_rows(rows)
  local lines = {}
  for _, row in ipairs(rows) do
    local cells = {}
    for _, cell in ipairs(row.cells) do
      table.insert(cells, blocks_to_latex(cell.contents))
    end
    table.insert(lines, table.concat(cells, " & ") .. " \\\\")
  end
  return table.concat(lines, "\n")
end

function Table(tbl)
  if not FORMAT:match("latex") then
    return tbl
  end
  local cap_tex = ""
  if tbl.caption and tbl.caption.long and #tbl.caption.long > 0 then
    cap_tex = blocks_to_latex(tbl.caption.long)
  end
  local label_tex = ""
  if tbl.identifier and tbl.identifier ~= "" then
    label_tex = "\\label{" .. tbl.identifier .. "}"
  end
  local col_spec = col_spec_for(tbl)
  local head_lines = render_rows(tbl.head.rows)
  local body_lines = {}
  for _, b in ipairs(tbl.bodies) do
    table.insert(body_lines, render_rows(b.body))
  end
  local out = {
    "\\begin{table}[tbp]",
    "\\centering",
    "\\small",
  }
  if cap_tex ~= "" then
    table.insert(out, "\\caption{" .. cap_tex .. "}" .. label_tex)
  elseif label_tex ~= "" then
    table.insert(out, label_tex)
  end
  table.insert(out, "\\begin{tabularx}{\\linewidth}{@{}" .. col_spec .. "@{}}")
  table.insert(out, "\\toprule")
  if head_lines ~= "" then
    table.insert(out, head_lines)
    table.insert(out, "\\midrule")
  end
  table.insert(out, table.concat(body_lines, "\n"))
  table.insert(out, "\\bottomrule")
  table.insert(out, "\\end{tabularx}")
  table.insert(out, "\\end{table}")
  return pandoc.RawBlock("latex", table.concat(out, "\n"))
end
