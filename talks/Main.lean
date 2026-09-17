import VersoSlides
import Slides

open VersoSlides

def layoutCss : CssFile where
  filename := "custom.css"
  contents := ⟨include_str "custom.css"⟩


def main : IO UInt32 :=
  slidesMain
    (config := {
      theme := "black"
      slideNumber := true
      transition := "slide"
      center := false
      extraCss := #[layoutCss]
    })
    (doc := %doc Slides)
