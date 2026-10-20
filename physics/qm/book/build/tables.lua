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
    if string.find(txt, "编号") then weights = {0.24, 0.07, 0.69}
    elseif string.find(txt, "标记") then weights = {0.10, 0.36, 0.54}
    else weights = {0.25, 0.34, 0.41} end
  elseif n == 4 then
    if string.find(txt, "Weyl") then weights = {0.18, 0.37, 0.13, 0.32}
    else weights = {0.21, 0.20, 0.28, 0.31} end
  else
    weights = {}
    for i=1,n do weights[i] = 1/n end
  end
  for i=1,n do t.colspecs[i][2] = weights[i] end
  return t
end
