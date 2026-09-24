#!/usr/bin/env python3
"""
Generate the Magma parity pages from ``parity/magma.toml``.

Usage::

    python3 parity/generate.py           # validate the data, regenerate every output
    python3 parity/generate.py --check   # fail if anything is invalid or out of date
    python3 parity/generate.py --sync    # add chapters that are new in the online Handbook

The outputs are ``parity/README.md`` (the full matrix), the charts
``parity/coverage-light.svg`` and ``parity/coverage-dark.svg``, and the
badge and summary blocks of the top-level ``README.md``.

Only the Python standard library is needed.
"""
import argparse
import html
import pathlib
import re
import sys
import time
import tomllib
import urllib.error
import urllib.parse
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
DATA = ROOT / 'parity' / 'magma.toml'
MATRIX = ROOT / 'parity' / 'README.md'
CHARTS = {theme: ROOT / 'parity' / f'coverage-{theme}.svg' for theme in ('light', 'dark')}
README = ROOT / 'README.md'
HANDBOOK = 'https://magma.maths.usyd.edu.au/magma/handbook/'

STATUSES = {
    'available': ('✅', 'Available'),
    'partial': ('🟡', 'Partial'),
    'missing': ('❌', 'Missing'),
    'n/a': ('➖', 'Not applicable'),
    'unassessed': ('⬜', 'Not assessed yet'),
}
ORIGINS = ('sage', 'calyx', 'both')
FIELDS = {'part', 'title', 'slug', 'intrinsics', 'status', 'summary', 'calyx',
          'origin', 'crosschecked', 'notes', 'issues'}
PACKAGE_FIELDS = {'name', 'url', 'status', 'summary', 'calyx', 'origin',
                  'crosschecked', 'notes', 'issues'}

THEMES = {
    'light': {'text': '#1f2328', 'muted': '#59636e', 'track': '#eff2f5',
              'available': '#1a7f37', 'partial': '#d4a72c', 'missing': '#cf222e',
              'n/a': '#8c959f', 'unassessed': '#d1d9e0'},
    'dark': {'text': '#f0f6fc', 'muted': '#9198a1', 'track': '#212830',
             'available': '#3fb950', 'partial': '#d29922', 'missing': '#f85149',
             'n/a': '#656c76', 'unassessed': '#3d444d'},
}
ORDER = ('available', 'partial', 'missing', 'n/a', 'unassessed')


# Loading and validation

def load():
    with open(DATA, 'rb') as f:
        data = tomllib.load(f)
    data.setdefault('chapter', [])
    data.setdefault('package', [])
    return data


def resolves(path):
    """
    Return whether the dotted path names a module, a package, or a name
    defined in a module under ``src/``.
    """
    parts = path.split('.')
    for n in range(len(parts), 0, -1):
        base = ROOT / 'src' / pathlib.Path(*parts[:n])
        rest = parts[n:]
        if base.is_dir() and not rest:
            return True
        for suffix in ('.py', '.pyx'):
            module = base.with_name(base.name + suffix)
            if module.is_file():
                if not rest:
                    return True
                source = module.read_text(encoding='utf-8', errors='replace')
                name = re.escape(rest[-1])
                pattern = (rf'^\s*(?:(?:async\s+)?def|cpdef|class|cdef\s+class|cdef)\s+'
                           rf'(?:[\w\[\], ]+\s+)?{name}\b|^\s*{name}\s*=')
                return len(rest) <= 2 and re.search(pattern, source, re.M) is not None
    return False


def validate(data):
    errors = []
    slugs = set()
    for i, entry in enumerate(data['chapter'] + data['package']):
        is_chapter = i < len(data['chapter'])
        where = entry.get('slug') if is_chapter else entry.get('name')
        where = f'{"chapter" if is_chapter else "package"} {where or i}'
        allowed = FIELDS if is_chapter else PACKAGE_FIELDS
        required = ({'part', 'title', 'slug', 'status'} if is_chapter
                    else {'name', 'url', 'status'})
        for key in sorted(required - entry.keys()):
            errors.append(f'{where}: missing field {key!r}')
        for key in sorted(entry.keys() - allowed):
            errors.append(f'{where}: unknown field {key!r}')
        status = entry.get('status')
        if status not in STATUSES:
            errors.append(f'{where}: status must be one of {", ".join(STATUSES)}')
        origin = entry.get('origin', '')
        if origin and origin not in ORIGINS:
            errors.append(f'{where}: origin must be one of {", ".join(ORIGINS)}')
        if status in ('available', 'partial'):
            if not entry.get('calyx'):
                errors.append(f'{where}: {status} needs at least one path in calyx')
            if not origin:
                errors.append(f'{where}: {status} needs an origin')
        for path in entry.get('calyx', []):
            if not resolves(path):
                errors.append(f'{where}: {path} does not exist under src/')
        if not isinstance(entry.get('issues', []), list):
            errors.append(f'{where}: issues must be a list of issue numbers')
        if is_chapter:
            if entry.get('slug') in slugs:
                errors.append(f'{where}: duplicate slug')
            slugs.add(entry.get('slug'))
    return errors


# Counting

def count(entries):
    tally = dict.fromkeys(ORDER, 0)
    for entry in entries:
        tally[entry['status']] += 1
    return tally


def parts(data):
    """The chapters grouped by Handbook part, in file order."""
    grouped = {}
    for chapter in data['chapter']:
        grouped.setdefault(chapter['part'], []).append(chapter)
    return grouped


def shown(data):
    """The statuses to display: always the first three, the others when used."""
    tally = count(data['chapter'])
    return [s for s in ORDER if s in ('available', 'partial', 'missing') or tally[s]]


def applicable(tally):
    return sum(tally.values()) - tally['n/a']


# Markdown

def bar(tally, width=10):
    total = applicable(tally)
    if not total:
        return '`' + '·' * width + '` n/a'
    share = (tally['available'] + tally['partial'] / 2) / total
    filled = round(width * share)
    return f'`{"█" * filled}{"░" * (width - filled)}` {round(100 * share)}%'


def badge(data):
    tally = count(data['chapter'])
    total = applicable(tally)
    share = tally['available'] / total if total else 0
    color = ('red' if share < 0.25 else 'orange' if share < 0.5
             else 'yellow' if share < 0.75 else 'brightgreen')
    message = urllib.parse.quote(f'{tally["available"]} of {total} chapters')
    return (f'[![Magma parity](https://img.shields.io/badge/Magma%20parity-{message}-{color})]'
            f'(parity/README.md)')


def summary_table(data, link_parts):
    statuses = shown(data)
    lines = ['| Handbook part | Coverage | ' + ' | '.join(STATUSES[s][0] for s in statuses) + ' |',
             '|---|---|' + '--:|' * len(statuses)]
    for part, chapters in parts(data).items():
        tally = count(chapters)
        name = f'[{part}](#{anchor(part)})' if link_parts else part
        lines.append(f'| {name} | {bar(tally)} | '
                     + ' | '.join(str(tally[s] or '·') for s in statuses) + ' |')
    tally = count(data['chapter'])
    lines.append(f'| **All {sum(tally.values())} chapters** | {bar(tally)} | '
                 + ' | '.join(f'**{tally[s]}**' for s in statuses) + ' |')
    return lines


def legend(data):
    return ' · '.join(f'{STATUSES[s][0]} {STATUSES[s][1].lower()}' for s in shown(data))


def headline(data):
    tally = count(data['chapter'])
    total = applicable(tally)
    text = (f'Of the {total} Handbook chapters that apply to Calyx, '
            f'{tally["available"]} are available and {tally["partial"]} partly available')
    if tally['unassessed']:
        text += f'; {tally["unassessed"]} are not assessed yet'
    return text + '.'


def anchor(heading):
    """GitHub's anchor for a heading."""
    return re.sub(r'[^\w\- ]', '', heading.lower()).replace(' ', '-')


def evidence(entry):
    links = []
    for path in entry.get('calyx', []):
        target = source_link(path)
        links.append(f'[`{path}`]({target})' if target else f'`{path}`')
    return '<br>'.join(links)


def source_link(path):
    parts = path.split('.')
    for n in range(len(parts), 0, -1):
        base = pathlib.Path('src', *parts[:n])
        if (ROOT / base).is_dir():
            return '../' + base.as_posix()
        for suffix in ('.py', '.pyx'):
            module = base.with_name(base.name + suffix)
            if (ROOT / module).is_file():
                return '../' + module.as_posix()
    return None


def cell(text):
    return ' '.join(str(text).split()).replace('|', '\\|')


def details(entry):
    notes = cell(entry.get('notes', ''))
    issues = ', '.join(f'[#{n}](https://github.com/aygerix/calyx-math/issues/{n})'
                       for n in entry.get('issues', []))
    return ' '.join([notes] + ([f'Issues: {issues}.'] if issues else [])).strip()


def status_cell(entry):
    """The status icon, marked when Calyx built it or checks it against Magma."""
    marks = []
    if entry.get('origin') in ('calyx', 'both'):
        marks.append('Calyx')
    if entry.get('crosschecked'):
        marks.append('checked')
    icon = STATUSES[entry['status']][0]
    return icon + (f'<br><sub>{" · ".join(marks)}</sub>' if marks else '')


def matrix(data):
    meta = data['handbook']
    out = [
        '<!-- Generated by parity/generate.py from parity/magma.toml. Do not edit by hand. -->',
        '',
        '# Magma parity',
        '',
        "This matrix tracks how much of Magma's functionality Calyx covers, chapter by chapter, "
        f'following the [Magma Handbook]({HANDBOOK}) ({meta["version"]}, {meta["date"]}). '
        f'{headline(data)}',
        '',
        f'**Status:** {legend(data)}. Coverage counts partial chapters as half.',
        '',
        '- **Available:** the core functionality of the chapter works in Calyx; the notes list what is still missing.',
        '- **Partial:** a substantial part works, but important functionality is missing or much weaker.',
        '- **Missing:** little or none of the chapter is available.',
        '- **Not applicable:** specific to the Magma language or environment, where Calyx uses Python instead, '
        'or an overview chapter with nothing to implement.',
        '',
        'Each chapter links to its Handbook page, and the **Calyx** column shows where the functionality lives. '
        'Functionality comes from SageMath unless the status is marked **Calyx**, meaning it was built or '
        'substantially extended in Calyx. **checked** means Calyx results are compared against Magma '
        'in a test harness.',
        '',
        'To change an entry, edit [`magma.toml`](magma.toml) and run `python3 parity/generate.py`. '
        'To ask for a missing feature, open a '
        '[Magma feature request](https://github.com/aygerix/calyx-math/issues/new?template=magma-feature.yml).',
        '',
        '## Summary',
        '',
        '<picture><source media="(prefers-color-scheme: dark)" srcset="coverage-dark.svg">'
        f'<img alt="{html.escape(headline(data))}" src="coverage-light.svg"></picture>',
        '',
    ]
    out += summary_table(data, link_parts=True)
    out.append('')
    for part, chapters in parts(data).items():
        part_tally = count(chapters)
        out += ['', f'## {part}', '',
                ' · '.join(f'{STATUSES[s][0]} {part_tally[s]}' for s in ORDER if part_tally[s]),
                '',
                '| Chapter | Status | Intrinsics | Calyx | Notes |',
                '|---|:-:|--:|---|---|']
        for chapter in chapters:
            title = f'[{chapter["title"]}]({HANDBOOK}{chapter["slug"]})'
            summary = cell(chapter.get('summary', ''))
            name = f'{title}<br><sub>{summary}</sub>' if summary else title
            out.append(f'| {name} | {status_cell(chapter)} | '
                       f'{chapter.get("intrinsics") or "·"} | {evidence(chapter)} | {details(chapter)} |')
    if data['package']:
        out += ['', '## Beyond the Handbook', '',
                'Magma packages that are distributed separately from Magma and are not in the Handbook.',
                '',
                '| Package | Status | Calyx | Notes |',
                '|---|:-:|---|---|']
        for package in data['package']:
            summary = cell(package.get('summary', ''))
            name = f'[{package["name"]}]({package["url"]})'
            name = f'{name}<br><sub>{summary}</sub>' if summary else name
            out.append(f'| {name} | {status_cell(package)} | '
                       f'{evidence(package)} | {details(package)} |')
    out.append('')
    return '\n'.join(out)


def readme_block(data):
    meta = data['handbook']
    lines = [
        f'Calyx tracks its coverage of Magma against the [Magma Handbook]({HANDBOOK}) '
        f'({meta["version"]}), chapter by chapter. {headline(data)} '
        'The [full matrix](parity/README.md) lists every chapter with its status, '
        'where it lives in Calyx, and what is still missing.',
        '',
        '<picture><source media="(prefers-color-scheme: dark)" srcset="parity/coverage-dark.svg">'
        f'<img alt="{html.escape(headline(data))}" src="parity/coverage-light.svg"></picture>',
        '',
        '<details>',
        '<summary>Coverage by Handbook part</summary>',
        '',
    ]
    lines += summary_table(data, link_parts=False)
    lines += ['', f'{legend(data)}. Coverage counts partial chapters as half.', '', '</details>']
    return '\n'.join(lines)


def replace_block(text, name, content):
    start, end = f'<!-- {name}:start -->', f'<!-- {name}:end -->'
    pattern = re.compile(re.escape(start) + r'.*?' + re.escape(end), re.S)
    if not pattern.search(text):
        raise SystemExit(f'README.md has no {start} ... {end} block')
    inline = '\n' not in content
    body = f'{start}{content}{end}' if inline else f'{start}\n{content}\n{end}'
    return pattern.sub(lambda _: body, text, count=1)


# Charts

def chart(data, theme):
    colors = THEMES[theme]
    grouped = parts(data)
    font = "-apple-system,BlinkMacSystemFont,'Segoe UI','Noto Sans',Helvetica,Arial,sans-serif"
    label_x, bar_x, bar_w, row_h, bar_h = 0, 232, 420, 22, 12
    top = 58
    width = bar_x + bar_w + 78
    height = top + row_h * len(grouped) + 6
    tally = count(data['chapter'])
    total = applicable(tally)
    out = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" role="img" aria-label="{html.escape(headline(data))}">',
        f'<title>{html.escape(headline(data))}</title>',
        f'<g font-family="{font}" font-size="12" fill="{colors["text"]}">',
        '<text x="0" y="16" font-size="14" font-weight="600">Magma Handbook coverage by part</text>',
        f'<text x="{width}" y="16" text-anchor="end" fill="{colors["muted"]}">'
        f'{tally["available"]} available · {tally["partial"]} partial · {total} applicable chapters</text>',
    ]
    x = 0
    for status in shown(data):
        label = STATUSES[status][1]
        out.append(f'<rect x="{x}" y="30" width="10" height="10" rx="2" fill="{colors[status]}"/>')
        out.append(f'<text x="{x + 15}" y="39" fill="{colors["muted"]}">{label}</text>')
        x += 15 + 7 * len(label) + 18
    for row, (part, chapters) in enumerate(grouped.items()):
        y = top + row * row_h
        part_tally = count(chapters)
        n = len(chapters)
        out.append(f'<text x="{label_x}" y="{y + 11}">{html.escape(part)}</text>')
        out.append(f'<clipPath id="r{row}"><rect x="{bar_x}" y="{y + 1}" width="{bar_w}" '
                   f'height="{bar_h}" rx="3"/></clipPath>')
        out.append(f'<g clip-path="url(#r{row})"><rect x="{bar_x}" y="{y + 1}" width="{bar_w}" '
                   f'height="{bar_h}" fill="{colors["track"]}"/>')
        offset = 0.0
        for status in ORDER:
            if part_tally[status]:
                w = bar_w * part_tally[status] / n
                out.append(f'<rect x="{bar_x + offset:.1f}" y="{y + 1}" width="{w:.1f}" '
                           f'height="{bar_h}" fill="{colors[status]}"/>')
                offset += w
        out.append('</g>')
        part_total = applicable(part_tally)
        label = f'{part_tally["available"]}/{part_total}' if part_total else 'n/a'
        out.append(f'<text x="{bar_x + bar_w + 10}" y="{y + 11}" fill="{colors["muted"]}">{label}</text>')
    out += ['</g>', '</svg>', '']
    return '\n'.join(out)


# Syncing with the online Handbook

def fetch(url):
    for wait in (1, 10, 30, 90):
        time.sleep(wait)
        try:
            request = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(request, timeout=60) as response:
                return response.read().decode('latin-1', errors='replace')
        except urllib.error.HTTPError as error:
            if error.code not in (429, 502, 503, 504):
                raise
    raise SystemExit(f'could not fetch {url}')


def title_case(title):
    small = {'a', 'an', 'and', 'as', 'at', 'by', 'for', 'in', 'of', 'on', 'or', 'over', 'the', 'to', 'with'}
    words = []
    for i, word in enumerate(title.split()):
        lower = word.lower()
        if i and lower in small:
            words.append(lower)
        elif len(word) <= 3 and word.isalpha() and word not in {'ONE', 'TWO', 'ALL', 'NEW'}:
            words.append(word if word in {'Q', 'R', 'C'} else word.capitalize())
        else:
            words.append('-'.join(piece.capitalize() for piece in lower.split('-')))
    return ' '.join(words)


def sync(data):
    """Add the chapters that are new in the online Handbook, as not assessed yet."""
    known = {chapter['slug'] for chapter in data['chapter']}
    front = fetch(HANDBOOK)
    online = []
    for path, part in re.findall(r'href="/magma/handbook/part/(\d+)">([^<]+)', front):
        page = fetch(f'{HANDBOOK}part/{path}')
        for slug, title in re.findall(r'<li><a\s+href\s*=\s*"/magma/handbook/([^"/]+)">(.*?)</a></li>', page):
            title = ' '.join(html.unescape(re.sub(r'<[^>]+>', '', title)).split())
            online.append((title_case(part.strip()), slug, title_case(title)))
    new = [(part, slug, title) for part, slug, title in online if slug not in known]
    gone = sorted(known - {slug for _, slug, _ in online})
    if new:
        with open(DATA, 'a', encoding='utf-8') as f:
            for part, slug, title in new:
                f.write(f'\n[[chapter]]\npart = "{part}"\ntitle = "{title}"\nslug = "{slug}"\n'
                        f'status = "unassessed"\n')
    for part, slug, title in new:
        print(f'added {part} / {title} ({slug}) as not assessed yet')
    for slug in gone:
        print(f'no longer in the Handbook: {slug}')
    if not new and not gone:
        print('parity/magma.toml already lists every Handbook chapter')


# Main

def outputs(data):
    readme = README.read_text(encoding='utf-8')
    readme = replace_block(readme, 'magma-parity-badge', badge(data))
    readme = replace_block(readme, 'magma-parity', readme_block(data))
    result = {MATRIX: matrix(data), README: readme}
    for theme, path in CHARTS.items():
        result[path] = chart(data, theme)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0].strip())
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true',
                      help='fail if the data is invalid or an output is out of date')
    mode.add_argument('--sync', action='store_true',
                      help='add chapters that are new in the online Handbook')
    args = parser.parse_args()

    data = load()
    if args.sync:
        sync(data)
        data = load()
    errors = validate(data)
    if errors:
        print('parity/magma.toml has problems:', *errors, sep='\n  ', file=sys.stderr)
        return 1
    stale = []
    for path, content in outputs(data).items():
        current = path.read_text(encoding='utf-8') if path.exists() else None
        if current != content:
            stale.append(path.relative_to(ROOT))
            if not args.check:
                path.write_text(content, encoding='utf-8')
    if args.check and stale:
        print('Out of date:', *stale, sep='\n  ', file=sys.stderr)
        print('Run python3 parity/generate.py and commit the result.', file=sys.stderr)
        return 1
    for path in ([] if args.check else stale):
        print(f'updated {path}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
