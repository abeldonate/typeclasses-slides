import VersoSlides
import Verso.Doc
import Demo.Chapter1
import Demo.Chapter2
import Demo.Chapter3
import Demo.Chapter4
import Demo.Chapter5
import Demo.Chapter6

open VersoSlides

namespace Demo

/-- Combined deck assembled from all six chapter documents. -/
def slidesDoc : Verso.Doc.Part Slides :=
  let ch1 : Verso.Doc.Part Slides := %doc Demo.Chapter1
  let ch2 : Verso.Doc.Part Slides := %doc Demo.Chapter2
  let ch3 : Verso.Doc.Part Slides := %doc Demo.Chapter3
  let ch4 : Verso.Doc.Part Slides := %doc Demo.Chapter4
  let ch5 : Verso.Doc.Part Slides := %doc Demo.Chapter5
  let ch6 : Verso.Doc.Part Slides := %doc Demo.Chapter6
  Verso.Doc.Part.mk
    ch1.title
    "VersoSlides Demo"
    ch1.metadata
    (ch1.content ++ ch2.content ++ ch3.content ++ ch4.content ++ ch5.content ++ ch6.content)
    (ch1.subParts ++ ch2.subParts ++ ch3.subParts ++ ch4.subParts ++ ch5.subParts ++ ch6.subParts)

end Demo
