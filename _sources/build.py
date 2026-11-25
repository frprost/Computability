#!/usr/bin/env python3
"""Builds the manual: python3 _sources/build.py  (from the site folder).

Optional: python3 _sources/build.py --out FOLDER  writes the pages to FOLDER
(the assets/ folder must then be copied there separately).

Each source page (_sources/pages/*.html) starts with a header:
    <!--
    titre: ...        (page title)
    court: ...        (label in the table of contents)
    chapo: ...        (optional lead paragraph)
    prerequis: a.html|Label ; b.html|Label   (optional prerequisites)
    -->
Convenience tags recognized in the body:
    <res type="Theorem" nom="..." id="..."> <enonce>..</enonce>
         <philo>..</philo> <tech>..</tech> <techno>..</techno> </res>
    <exo niveau="1|2|3" titre="..." id="..."> statement <corrige>..</corrige> </exo>
    <preuve>..</preuve>
(The tag and attribute names are those of the French edition, so that both
editions share the same source format.)
"""
import html
import os
import re
import sys
import unicodedata

HERE = os.path.dirname(os.path.abspath(__file__))
SITE = os.path.dirname(HERE)
if "--out" in sys.argv:
    SITE = os.path.abspath(sys.argv[sys.argv.index("--out") + 1])

# (file, group) in reading order
PAGES = [
    ("index.html", None),
    ("motivations.html", "Getting started"),
    ("three-approaches.html", "Getting started"),
    ("turing-machines.html", "Models of computation"),
    ("recursive-functions.html", "Models of computation"),
    ("lambda-calculus.html", "Models of computation"),
    ("equivalence.html", "Models of computation"),
    ("church-turing-thesis.html", "Models of computation"),
    ("universality.html", "Fundamental theorems"),
    ("smn-recursion.html", "Fundamental theorems"),
    ("undecidability.html", "Limits of computation"),
    ("semi-decidability.html", "Limits of computation"),
    ("arithmetical-hierarchy.html", "Limits of computation"),
    ("incompleteness.html", "Limits of computation"),
    ("diophantine-equations.html", "Limits of computation"),
    ("logic-and-types.html", "Limits of computation"),
    ("decidable-theories.html", "Limits of computation"),
    ("undecidable-mathematics.html", "Limits of computation"),
    ("kolmogorov-omega.html", "Limits of computation"),
    ("languages.html", "Limits of computation"),
    ("complexity.html", "Complexity"),
    ("randomness-quantum.html", "Complexity"),
    ("ackermann.html", "Case studies"),
    ("busy-beavers.html", "Case studies"),
    ("computability-ai.html", "Case studies"),
    ("other-models.html", "Case studies"),
    ("reading-paths.html", "Appendices"),
    ("cantor.html", "Appendices"),
    ("bases.html", "Appendices"),
    ("leibniz.html", "Appendices"),
    ("bibliography.html", "Appendices"),
]
UNNUMBERED = "Appendices"
TYPES_DEF = {"Definition", "Notation", "Convention", "Example"}


def slug(s):
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode()
    s = re.sub(r"<[^>]+>", "", s)
    s = re.sub(r"\$[^$]*\$", "", s)
    s = re.sub(r"[^a-zA-Z0-9]+", "-", s).strip("-").lower()
    return s or "section"


def read_page(name):
    with open(os.path.join(HERE, "pages", name), encoding="utf-8") as f:
        src = f.read()
    m = re.match(r"\s*<!--(.*?)-->", src, re.S)
    meta = {}
    if m:
        for line in m.group(1).strip().splitlines():
            if ":" in line:
                k, v = line.split(":", 1)
                meta[k.strip()] = v.strip()
        src = src[m.end():]
    return meta, src


def attr(s, name):
    m = re.search(name + r'="([^"]*)"', s)
    return m.group(1) if m else ""


def escape_math(body):
    """Inside $...$ and $$...$$, "<A" would be read as an HTML tag: write &lt; instead."""
    return re.sub(r"\$\$.*?\$\$|\$[^$\n]+?\$",
                  lambda m: re.sub(r"<(?=[A-Za-z/!])", "&lt;", m.group(0)), body, flags=re.S)


def transform(body, page, result_index):
    body = escape_math(body)

    def res(m):
        a = m.group(1)
        typ, name, ident = attr(a, "type") or "Theorem", attr(a, "nom"), attr(a, "id")
        if not ident:
            ident = slug(name)
        result_index.append((name, typ, page, ident))
        cls = "definition" if typ in TYPES_DEF else "theoreme"
        return ('<div class="resultat %s" id="%s"><div class="entete-res"><div class="type">%s</div>'
                '<div class="nom">%s</div></div>' % (cls, ident, typ, name))
    body = re.sub(r"<res\b([^>]*)>", res, body)
    body = body.replace("</res>", "</div>")
    body = re.sub(r"<enonce>", '<div class="enonce">', body)
    for n in ("philo", "tech", "techno"):
        body = re.sub(r"<%s>" % n, '<div class="niveau" data-niveau="%s">' % n, body)
    body = re.sub(r"</(enonce|philo|tech|techno)>", "</div>", body)
    body = re.sub(r"<preuve>", '<div class="preuve">', body).replace("</preuve>", "</div>")
    counter = [0]

    def exo(m):
        a = m.group(1)
        counter[0] += 1
        level = int(attr(a, "niveau") or "1")
        ident = attr(a, "id") or "exercise-%d" % counter[0]
        t = attr(a, "titre")
        legend = ""
        if counter[0] == 1:
            legend = ('<p class="legende-exo">Levels: ★ direct application of the course, ★★ standard exercise, '
                      '★★★ going further. Solutions are hidden: click “Solution” to show them.</p>')
        return ('%s<div class="exercice" id="%s"><div class="entete-exo"><span class="etoiles" title="level %d">%s</span>'
                '<span class="nom-exo">Exercise %d%s</span></div><div class="corps-exo">'
                % (legend, ident, level, "★" * level, counter[0], (" — " + t) if t else ""))
    body = re.sub(r"<exo\b([^>]*)>", exo, body)
    body = body.replace("</exo>", "</div></div>")
    body = body.replace("<corrige>", '<details class="corrige"><summary>Solution</summary><div class="texte-corrige">')
    body = body.replace("</corrige>", "</div></details>")
    # ids of the h2/h3 sections
    toc = []
    seen = set()

    def heading(m):
        lvl, attrs, txt = m.group(1), m.group(2), m.group(3)
        ident = attr(attrs, "id") or slug(txt)
        base, k = ident, 2
        while ident in seen:
            ident = "%s-%d" % (base, k)
            k += 1
        seen.add(ident)
        if lvl == "2":
            toc.append((ident, re.sub(r"<[^>]+>", "", txt)))
        return '<h%s id="%s">%s</h%s>' % (lvl, ident, txt, lvl)
    body = re.sub(r"<h([23])((?:\s[^>]*)?)>(.*?)</h\1>", heading, body, flags=re.S)
    return body, toc


def template(meta, body, toc, name, previous, following, contents):
    title = meta.get("titre", "")
    head_title = "Computability" if name == "index.html" else title + " · Computability"
    prereq = ""
    if meta.get("prerequis"):
        links = []
        for item in meta["prerequis"].split(";"):
            if "|" in item:
                f, l = item.split("|", 1)
                links.append('<a href="%s">%s</a>' % (f.strip(), l.strip()))
            else:
                links.append(item.strip())
        prereq = '<div class="prerequis"><strong>Prerequisites</strong>%s</div>' % " · ".join(links)
    toc_html = ""
    if len(toc) >= 3 and name != "index.html":
        toc_html = '<nav class="toc-locale" aria-label="In this chapter"><strong>In this chapter</strong><ol>%s</ol></nav>' % "".join(
            '<li><a href="#%s">%s</a></li>' % (i, t) for i, t in toc)
    nav = '<nav class="nav-chap">'
    if previous:
        nav += '<a href="%s"><small>← Previous</small>%s</a>' % previous
    else:
        nav += "<span></span>"
    if following:
        nav += '<a href="%s" style="text-align:right"><small>Next →</small>%s</a>' % following
    nav += "</nav>"
    lead = '<p class="chapo">%s</p>' % meta["chapo"] if meta.get("chapo") else ""
    return """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="author" content="Frédéric Prost and Claude">
<title>{head_title}</title>
<link rel="stylesheet" href="assets/katex/katex.min.css">
<link rel="stylesheet" href="assets/style.css">
<script>try{{var t=localStorage.getItem('calc-theme');if(t)document.documentElement.setAttribute('data-theme',t);}}catch(e){{}}document.documentElement.classList.add('js');</script>
</head>
<body>
<header class="entete"><div class="entete-int">
  <button type="button" class="btn-menu" aria-label="Contents">☰ Contents</button>
  <a class="titre-site" href="index.html">Computability <span>·</span> a manual with three reading levels</a>
  <span class="selecteur-legende">Reading level:</span>
  <div class="selecteur" role="group" aria-label="Reading level">
    <button type="button" data-niveau="philo" title="Meaning and implications">Philosophical</button>
    <button type="button" data-niveau="tech" title="Mathematical proofs">Technical</button>
    <button type="button" data-niveau="techno" title="Complete constructions, Turing machines">Technological</button>
    <button type="button" data-niveau="tout" title="Show all three levels">All</button>
  </div>
  <button type="button" class="btn-theme" aria-label="Change theme" title="Light / dark">◐</button>
</div></header>
<div class="page">
<nav class="sommaire" aria-label="Contents">{contents}</nav>
<main class="contenu">
<h1>{title}</h1>
{lead}
{prereq}
{toc}
{body}
{nav}
<footer class="pied">Computability — a manual with three reading levels. Authors: Frédéric Prost and Claude. Text licensed under <a href="https://creativecommons.org/licenses/by-sa/4.0/" rel="license">CC BY-SA 4.0</a>, code under the MIT licence. Mathematics is rendered by KaTeX (MIT licence), bundled locally: the site can be read offline.</footer>
</main>
</div>
<script src="assets/katex/katex.min.js"></script>
<script src="assets/katex/contrib/auto-render.min.js"></script>
<script src="assets/turing.js"></script>
<script src="assets/lambda.js"></script>
<script src="assets/pcp.js"></script>
<script src="assets/automates.js"></script>
<script src="assets/niveaux.js"></script>
<script src="assets/widgets.js"></script>
</body>
</html>
""".format(head_title=html.escape(head_title), title=title, lead=lead, prereq=prereq, toc=toc_html,
           body=body, nav=nav, contents=contents)


def build():
    metas, sources = {}, {}
    for name, _ in PAGES:
        metas[name], sources[name] = read_page(name)

    def contents(active):
        h, group, num = "", None, 0
        h += '<ul><li><a href="index.html"%s>Home and how to use this manual</a></li></ul>' % (
            ' aria-current="page"' if active == "index.html" else "")
        for name, g in PAGES[1:]:
            if g != group:
                if group is not None:
                    h += "</ol>"
                h += "<h2>%s</h2><ol>" % g
                group = g
            short = metas[name].get("court") or metas[name].get("titre")
            pref = ""
            if g != UNNUMBERED:
                num += 1
                pref = '<span class="num">%d</span>' % num
            h += '<li><a href="%s"%s>%s%s</a></li>' % (name, ' aria-current="page"' if name == active else "", pref, short)
        return h + "</ol>"
    result_index = []
    rendered = {}
    for name, _ in PAGES:
        rendered[name] = transform(sources[name], name, result_index)
    # alphabetical index of results, injected into the home page

    def key(t):
        return unicodedata.normalize("NFKD", re.sub(r"<[^>]+>|\$", "", t[0])).encode("ascii", "ignore").decode().lower()
    alpha = "".join('<li><a href="%s#%s">%s</a> <small>(%s)</small></li>' % (p, i, n, t.lower())
                    for n, t, p, i in sorted(result_index, key=key))
    body, toc = rendered["index.html"]
    body = body.replace("<!--INDEX-ALPHA-->", '<ul class="alpha">%s</ul>' % alpha)
    themes, group = "", None
    for name, g in PAGES[1:]:
        if g != group:
            if group is not None:
                themes += "</ul></div>"
            themes += '<div class="carte"><h4>%s</h4><ul>' % g
            group = g
        themes += '<li><a href="%s">%s</a></li>' % (name, metas[name].get("court") or metas[name]["titre"])
    themes += "</ul></div>"
    body = body.replace("<!--THEMES-->", '<div class="cartes">%s</div>' % themes)
    rendered["index.html"] = (body, toc)
    for k, (name, _) in enumerate(PAGES):
        prev = (PAGES[k - 1][0], metas[PAGES[k - 1][0]]["titre"]) if k > 0 else None
        nxt = (PAGES[k + 1][0], metas[PAGES[k + 1][0]]["titre"]) if k + 1 < len(PAGES) else None
        body, toc = rendered[name]
        out = template(metas[name], body, toc, name, prev, nxt, contents(name))
        with open(os.path.join(SITE, name), "w", encoding="utf-8") as f:
            f.write(out)
    print("%d pages, %d results indexed" % (len(PAGES), len(result_index)))


if __name__ == "__main__":
    build()
