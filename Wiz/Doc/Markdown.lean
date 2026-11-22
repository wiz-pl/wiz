import Wiz.Doc.Highlight

/-!
# Markdown, for doc comments (stage 11s)

A small subset, enough for documentation: paragraphs, ATX headings (`#`…), fenced code
blocks (```` ``` ````), indented code is not special, bullet (`*`, `-`) and numbered
(`1.`) lists, block quotes (`>`), and inline `code`, `*emphasis*`, `**strong**`,
`[links](url)`. Everything else is text (HTML in the input is escaped, never passed on).
`link` resolves a name in backticks to a URL (a declaration's page), if it is one.

A fenced block tagged `wiz` is highlighted at render time with the parser's own token
reader (`Wiz.Doc.Highlight`); a block with no tag stays plain, and one with an unknown
tag is plain too. `renderWith` also returns the blocks' spans, which the documentation
page carries as data for the interactive hover (`wizHighlight`). `renderPlain` is the
pre-highlighting renderer, for `--no-highlight` and the lossless Markdown manual.
-/

namespace Wiz.Doc

/-- A URL is kept only if it is relative or http(s)/mailto (no `javascript:`). -/
def safeUrl (u : String) : Bool :=
  let l := u.toLower
  !(l.startsWith "javascript:" || l.startsWith "data:" || l.startsWith "vbscript:")

/-- Inline Markdown on one paragraph's text. -/
partial def inline (link : String → Option String) (s : String) : String :=
  go s.toList ""
where
  go : List Char → String → String
    | [], acc => acc
    | '`' :: rest, acc =>
      let code := rest.takeWhile (· != '`')
      if code.length == rest.length then go rest (acc ++ "`") else
      let text := String.ofList code
      let html := s!"<code>{htmlEscape text}</code>"
      let html := match link text with
        | some u => s!"<a href=\"{htmlEscape u}\">{html}</a>"
        | none => html
      go (rest.drop (code.length + 1)) (acc ++ html)
    | '*' :: '*' :: rest, acc => match close ['*', '*'] rest [] with
      | some (inner, after) => go after (acc ++ s!"<strong>{inline link (String.ofList inner)}</strong>")
      | none => go rest (acc ++ "**")
    | '*' :: rest, acc => match close ['*'] rest [] with
      | some (inner, after) =>
        if inner.isEmpty || inner.head? == some ' ' then go rest (acc ++ "*")
        else go after (acc ++ s!"<em>{inline link (String.ofList inner)}</em>")
      | none => go rest (acc ++ "*")
    | '[' :: rest, acc =>
      let label := rest.takeWhile (· != ']')
      let after := rest.drop (label.length + 1)
      match decide (label.length < rest.length), after with
      | true, '(' :: more =>
        let url := more.takeWhile (· != ')')
        if url.length == more.length then go rest (acc ++ "[") else
        let u := String.ofList url
        if safeUrl u then
          go (more.drop (url.length + 1)) (acc ++ s!"<a href=\"{htmlEscape u}\">{inline link (String.ofList label)}</a>")
        else go (more.drop (url.length + 1)) (acc ++ inline link (String.ofList label))
      | _, _ => go rest (acc ++ "[")
    | c :: rest, acc => go rest (acc ++ htmlEscape c.toString)
  /-- the text up to the closing `delim` (not inside `code`), and what follows it -/
  close (delim : List Char) : List Char → List Char → Option (List Char × List Char)
    | [], _ => none
    | c :: rest, acc =>
      let cs := c :: rest
      if cs.take delim.length == delim then some (acc.reverse, cs.drop delim.length)
      else if c == '`' then
        let code := rest.takeWhile (· != '`')
        close delim (rest.drop (code.length + 1)) ('`' :: (code.reverse ++ '`' :: acc))
      else close delim rest (c :: acc)

def isBullet (l : String) : Bool := l.startsWith "* " || l.startsWith "- "
def numbered? (l : String) : Option String :=
  let ds := l.toList.takeWhile Char.isDigit
  if ds.isEmpty then none else
  match l.toList.drop ds.length with
  | '.' :: ' ' :: rest => some (String.ofList rest)
  | _ => none

/-- A rendered Markdown fragment and its fenced blocks in reading order (the page
data's `wizHighlight` blocks): a highlighted block has its spans, a plain one none, so
the block index is the fence's position in the Markdown. -/
structure Rendered where
  html : String
  blocks : Array Highlight.Block := #[]
  deriving Inhabited

/-- Markdown → HTML and the highlighted blocks. `tokens` is the module's parser table
(`CommandState.tables.tokens`), so a `wiz` fence agrees with the module's own syntax; with
`highlight := false` the output is exactly the pre-highlighting renderer. -/
partial def renderWith (link : String → Option String) (reg : Highlight.Registry)
    (tokens : Array String) (highlight : Bool) (src : String) : Rendered :=
  let (html, blocks) := blocks (src.splitOn "\n") ("", #[])
  { html, blocks }
where
  /-- A fence: its HTML and, if it is a highlighted `wiz` block, its spans. -/
  fence (lang body : String) : String × Option Highlight.Block :=
    let lang := lang.trimAscii.toString
    if !highlight then
      let cls := if lang.isEmpty then "" else s!" class=\"language-{htmlEscape lang}\""
      (s!"<pre><code{cls}>{htmlEscape body}</code></pre>\n", none)
    else match Highlight.blockOf reg tokens lang body with
      | some b =>
        (s!"<pre><code class=\"language-{htmlEscape b.language}\">{Highlight.html b.spans body}</code></pre>\n", some b)
      | none =>
        -- (an untagged or unknown block is plain; it still records an empty block so a
        -- `wizHighlight` index is the n-th fence, the runtime's numbering)
        let cls := if lang.isEmpty then "" else " class=\"language-unknown\""
        (s!"<pre><code{cls}>{htmlEscape body}</code></pre>\n",
          some { language := Highlight.languageOf lang, source := body, spans := #[] })
  blocks : List String → String × Array Highlight.Block → String × Array Highlight.Block
    | [], acc => acc
    | l :: ls, (accHtml, accBlocks) =>
      let t := l.trimAscii.toString
      if t.isEmpty then blocks ls (accHtml, accBlocks)
      else if t.startsWith "```" then
        let lang := (t.drop 3).trimAscii.toString
        let body := ls.takeWhile (!·.trimAscii.startsWith "```")
        let (fenceHtml, blk) := fence lang ("\n".intercalate body)
        let accBlocks := match blk with | some b => accBlocks.push b | none => accBlocks
        blocks (ls.drop (body.length + 1)) (accHtml ++ fenceHtml, accBlocks)
      else if t.startsWith "#" then
        let n := min 6 (t.toList.takeWhile (· == '#')).length
        let text := (t.drop n).trimAscii.toString
        -- (headings in a doc comment sit under the declaration's own: start at h4)
        let h := min 6 (n + 3)
        blocks ls (accHtml ++ s!"<h{h}>{inline link text}</h{h}>\n", accBlocks)
      else if isBullet t || (numbered? t).isSome then
        let ordered := (numbered? t).isSome
        let (items, rest) := listItems ordered (l :: ls) #[]
        let tag := if ordered then "ol" else "ul"
        let lis := items.toList.map fun i => s!"<li>{inline link i}</li>"
        blocks rest (accHtml ++ s!"<{tag}>{String.join lis}</{tag}>\n", accBlocks)
      else if t.startsWith ">" then
        let quoted := (l :: ls).takeWhile (·.trimAscii.startsWith ">")
        let inner := quoted.map fun q => ((q.trimAscii.drop 1).toString)
        let inner := renderWith link reg tokens highlight ("\n".intercalate inner)
        blocks (ls.drop (quoted.length - 1))
          (accHtml ++ s!"<blockquote>{inner.html}</blockquote>\n", accBlocks ++ inner.blocks)
      else
        let para := (l :: ls).takeWhile fun p =>
          let p := p.trimAscii.toString
          !p.isEmpty && !p.startsWith "```" && !p.startsWith "#" && !isBullet p && (numbered? p).isNone && !p.startsWith ">"
        let para := if para.isEmpty then [l] else para
        blocks (ls.drop (para.length - 1))
          (accHtml ++ s!"<p>{inline link (" ".intercalate (para.map (·.trimAscii.toString)))}</p>\n", accBlocks)
  /-- a list's items (continuation lines are indented) -/
  listItems (ordered : Bool) : List String → Array String → Array String × List String
    | [], acc => (acc, [])
    | l :: ls, acc =>
      let t := l.trimAscii.toString
      let item? := if ordered then numbered? t else if isBullet t then some (t.drop 2).toString else none
      match item? with
      | some i => listItems ordered ls (acc.push i)
      | none =>
        if !t.isEmpty && l.startsWith " " && !acc.isEmpty then
          listItems ordered ls (acc.modify (acc.size - 1) (· ++ " " ++ t))
        else (acc, l :: ls)

/-- Markdown → HTML, with `wiz` fences highlighted by the built-in token table. -/
def render (link : String → Option String) (src : String) : String :=
  (renderWith link Highlight.Registry.builtins Highlight.builtinTokens true src).html

/-- Markdown → HTML exactly as before highlighting (`--no-highlight`, and the Markdown
reference, where spans have no lossless form). -/
def renderPlain (link : String → Option String) (src : String) : String :=
  (renderWith link Highlight.Registry.builtins Highlight.builtinTokens false src).html

end Wiz.Doc
