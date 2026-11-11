function Table(t)
  local n = #t.colspecs
  local txt = ""
  for _, row in ipairs(t.head.rows) do
    for _, cell in ipairs(row.cells) do
      txt = txt .. " " .. pandoc.utils.stringify(cell.contents)
    end
  end
  local weights
  if n == 2 then weights = {0.30, 0.70}
  elseif n == 3 then
    if (string.find(txt, "模块") and string.find(txt, "定理")) or
       (string.find(txt, "Module") and string.find(txt, "theorems")) then weights = {0.30, 0.12, 0.58}
    elseif string.find(txt, "Result ID") or
       (string.find(txt, "ID") and string.find(txt, "Chapter") and string.find(txt, "Result")) then weights = {0.24, 0.10, 0.66}
    elseif string.find(txt, "编号") then weights = {0.24, 0.07, 0.69}
    elseif string.find(txt, "标记") or string.find(txt, "Marker") then weights = {0.10, 0.36, 0.54}
    else weights = {0.25, 0.34, 0.41} end
  elseif n == 4 then
    if string.find(txt, "Weyl") then weights = {0.18, 0.37, 0.13, 0.32}
    else weights = {0.21, 0.20, 0.28, 0.31} end
  elseif n == 5 and string.find(txt, "Source file") then
    weights = {0.40, 0.18, 0.10, 0.10, 0.22}
  else
    weights = {}
    for i=1,n do weights[i] = 1/n end
  end
  for i=1,n do t.colspecs[i][2] = weights[i] end
  return t
end
