-- Keep tables unbroken on a single page with their explanatory captions.
-- Publication-only layout helper; see COPYRIGHT_AND_LICENSE.md.
function Table(element)
  if FORMAT:match("latex") then
    return {pandoc.RawBlock("latex", "\\Needspace{24\\baselineskip}"), element}
  end
  return element
end
