-- Keep each comparison table intact on a single page with its caption.
-- Publication-only layout helper; see COPYRIGHT_AND_LICENSE.md.
function Table(element)
  if FORMAT:match("latex") then
    return {pandoc.RawBlock("latex", "\\Needspace{24\\baselineskip}"), element}
  end
  return element
end
