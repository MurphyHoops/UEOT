-- Keep this article's compact comparison table with its explanatory caption.
-- Publication-only layout helper; see COPYRIGHT_AND_LICENSE.md.
function Table(element)
  if FORMAT:match("latex") then
    return {pandoc.RawBlock("latex", "\\Needspace{16\\baselineskip}"), element}
  end
  return element
end
