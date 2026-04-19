import VersoSlides
import Verso.Doc
import Demo.Chapter1
import Demo.Chapter2

open VersoSlides

namespace Demo

/-- Combined deck assembled from the two chapter documents. -/
def slidesDoc : Verso.Doc.Part Slides :=
  let ch1 : Verso.Doc.Part Slides := %doc Demo.Chapter1
  let ch2 : Verso.Doc.Part Slides := %doc Demo.Chapter2
  Verso.Doc.Part.mk
    ch1.title
    "VersoSlides Demo"
    ch1.metadata
    (ch1.content ++ ch2.content)
    (ch1.subParts ++ ch2.subParts)

end Demo
