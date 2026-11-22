-- Keep comparison and benchmark tables unbroken with their captions.
-- Publication-only layout helper; see COPYRIGHT_AND_LICENSE.md.
function Table(element)
  if FORMAT:match("latex") then
    return {pandoc.RawBlock("latex", "\\Needspace{14\\baselineskip}"), element}
  end
  return element
end
