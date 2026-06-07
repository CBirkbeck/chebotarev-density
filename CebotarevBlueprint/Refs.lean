import Verso
import VersoManual
import VersoBlueprint
import VersoManual.Bibliography

open Verso
open Verso.Genre
open Verso.Genre.Manual
open Informal

/-!
# Bibliography entries for the Chebotarev density blueprint

Each entry is a `Verso.Genre.Manual.Bibliography.Citable` tagged with a
`@[bib "label"]` attribute. The labels are referenced from the chapter prose
via `{Informal.citet <label> ...}[]` / `{Informal.citep <label> ...}[]` roles
and rendered as a list by the `{blueprint_bibliography}` directive in
`Blueprint.lean`.
-/

@[bib "sharifi"]
def sharifi : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Algebraic Number Theory (course notes)"
  , authors := #[inlines!"Romyar Sharifi"]
  , journal := inlines!"Lecture notes, UCLA"
  , year := 2025
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := some "https://www.math.ucla.edu/~sharifi/algnum.pdf"
  }

@[bib "stevenhagen-lenstra"]
def stevenhagenLenstra : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Chebotarëv and his density theorem"
  , authors := #[inlines!"Peter Stevenhagen", inlines!"Hendrik W. Lenstra, Jr."]
  , journal := inlines!"The Mathematical Intelligencer"
  , year := 1996
  , month := none
  , volume := inlines!"18"
  , number := inlines!"2"
  , pages := some (26, 37)
  }

@[bib "gun-ramare-sivaraman"]
def gunRamareSivaraman : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Counting ideals in ray classes"
  , authors := #[inlines!"Sanoli Gun", inlines!"Olivier Ramaré", inlines!"Jyothsnaa Sivaraman"]
  , journal := inlines!"Journal of Number Theory"
  , year := 2023
  , month := none
  , volume := inlines!"243"
  , number := inlines!""
  , pages := none
  }

@[bib "lang-ant"]
def langAnt : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"Algebraic Number Theory"
  , authors := #[inlines!"Serge Lang"]
  , journal := inlines!"Graduate Texts in Mathematics 110, Springer-Verlag"
  , year := 1994
  , month := none
  , volume := inlines!""
  , number := inlines!""
  }
