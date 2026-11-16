// fast-marked — dependency-free CommonMark 0.31.2 + GFM 0.29 parser.
// Written from scratch to match marked 18.1.3 default output (GFM on)
// byte-for-byte. No dependencies, plain modern JS (Node 22/26 target).

// ---------------------------------------------------------------- utilities

// Escape &, <, >, ", ' — the "no-encode" variant: an & is left alone when it
// starts a valid entity pattern (&word; / &#digits; / &#xhex;), otherwise &amp;.
const NO_ENCODE_AMP = /&(?!(?:#\d{1,7};|#[xX][0-9a-fA-F]{1,6};|\w+;))/g;
function escNoEncode(s) {
  return s.replace(NO_ENCODE_AMP, '&amp;')
    .replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}
// Encode variant (code spans / code blocks): every & becomes &amp;.
function escEncode(s) {
  return s.replace(/&/g, '&amp;')
    .replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}
// Text escaping for inline content: & no-encode, < > " ' escaped.
// (marked escapes quotes in text too.)
function escText(s) {
  return s.replace(NO_ENCODE_AMP, '&amp;')
    .replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}

// Decode numeric character references only (named entities pass through raw,
// matching marked). Valid: &#1-7 decimal digits; / &#x|&#X 1-6 hex digits.
// Out of range / surrogate -> U+FFFD.
const NUMREF_RE = /&(#\d{1,7};|#[xX][0-9a-fA-F]{1,6};)/g;
function decodeNumericRefs(s) {
  if (s.indexOf('&#') === -1) return s;
  return s.replace(NUMREF_RE, (m, body) => {
    let cp;
    if (body[1] === 'x' || body[1] === 'X') cp = parseInt(body.slice(2, -1), 16);
    else cp = parseInt(body.slice(1, -1), 10);
    if (cp === 0 || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)) cp = 0xFFFD;
    return String.fromCodePoint(cp);
  });
}

// cleanUrl: encodeURI(href) with %25 restored to %, then attribute-escape.
function cleanUrl(href) {
  try { href = encodeURI(href).replace(/%25/g, '%'); } catch (e) { return null; }
  return href;
}
function escAttr(s) { return escNoEncode(s); }

// ASCII punctuation set for backslash escapes.
const PUNCT = new Set('!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~'.split(''));

// ---------------------------------------------------------------- inline parser
// Delimiter-stack algorithm (CommonMark Appendix A), with ~ strikethrough.

const BLOCK_TAGS = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param search section summary table tbody td tfoot th thead title tr track ul').split(' '));

// Match a raw HTML tag / comment / PI / declaration / CDATA at pos i.
// Returns end index (exclusive) or -1.
function matchHtmlTag(s, i) {
  const n = s.length;
  if (s[i] !== '<') return -1;
  // comment (abruptly-closed empty comments <!--> and <!---> end at the >)
  if (s.startsWith('<!--', i)) {
    if (s[i + 4] === '>') return i + 5;
    if (s[i + 4] === '-' && s[i + 5] === '>') return i + 6;
    const e = s.indexOf('-->', i + 4);
    return e === -1 ? -1 : e + 3;
  }
  // processing instruction
  if (s.startsWith('<?', i)) {
    const e = s.indexOf('?>', i + 2);
    return e === -1 ? -1 : e + 2;
  }
  // declaration
  if (s.startsWith('<!', i)) {
    const c = s[i + 2];
    if (c === undefined) return -1;
    if (/[A-Za-z]/.test(c)) {
      const e = s.indexOf('>', i + 2);
      return e === -1 ? -1 : e + 1;
    }
    if (s.startsWith('<![CDATA[', i)) {
      const e = s.indexOf(']]>', i + 9);
      return e === -1 ? -1 : e + 3;
    }
    return -1;
  }
  // open / close tag
  let j = i + 1;
  let closing = false;
  if (s[j] === '/') { closing = true; j++; }
  if (j >= n || !/[A-Za-z]/.test(s[j])) return -1;
  while (j < n && /[A-Za-z0-9-]/.test(s[j])) j++;
  // closing tags take no attributes: only optional whitespace then >
  if (closing) {
    while (j < n && (s[j] === ' ' || s[j] === '\t' || s[j] === '\n')) j++;
    return (j < n && s[j] === '>') ? j + 1 : -1;
  }
  // attributes: each must be preceded by whitespace (so <m:abc> is
  // not a tag: the : follows the tag name with no whitespace)
  while (true) {
    let sawWS = false;
    while (j < n && (s[j] === ' ' || s[j] === '\t' || s[j] === '\n')) { j++; sawWS = true; }
    if (j >= n) return -1;
    if (s[j] === '>') return j + 1;
    if (s[j] === '/' && s[j + 1] === '>') return j + 2;
    if (!sawWS) return -1;
    if (!/[_A-Za-z:]/.test(s[j])) return -1;
    while (j < n && /[A-Za-z0-9_.:-]/.test(s[j])) j++;
    // optional whitespace then = value? peek with k so a valueless
    // attribute does not consume the separator before the next one
    let k = j;
    while (k < n && (s[k] === ' ' || s[k] === '\t' || s[k] === '\n')) k++;
    if (s[k] === '=') {
      j = k + 1;
      while (j < n && (s[j] === ' ' || s[j] === '\t' || s[j] === '\n')) j++;
      if (j >= n) return -1;
      const q = s[j];
      if (q === '"' || q === "'") {
        j++;
        while (j < n && s[j] !== q) j++;
        if (j >= n) return -1;
        j++;
      } else {
        if (j >= n || /[\s"'=<`>]/.test(s[j])) return -1;
        while (j < n && !/[\s"'=<`>]/.test(s[j])) j++;
      }
    }
  }
}

// GFM extended autolink helpers.
const TRIM_CHARS = new Set('?!.,:;*_~"\'');
function trimExtendedUrl(u) {
  // Greedy match already applied; apply the trim loop.
  while (u.length > 0) {
    // entity pattern at end: &[A-Za-z0-9][A-Za-z0-9]*;
    const m = /&[A-Za-z0-9][A-Za-z0-9]*;$/.exec(u);
    if (m) { u = u.slice(0, u.length - m[0].length); continue; }
    const last = u[u.length - 1];
    if (TRIM_CHARS.has(last)) { u = u.slice(0, -1); continue; }
    if (last === ')') {
      let open = 0, close = 0;
      for (let k = 0; k < u.length; k++) { if (u[k] === '(') open++; else if (u[k] === ')') close++; }
      if (u.endsWith('))') || close > open) { u = u.slice(0, -1); continue; }
    }
    if (last === ']') {
      // a ] after an unmatched ) means the URL sits inside a link dest
      // ( ... ) and the ] is the outer link bracket, not part of the URL
      // (e.g. https://e.com)*] ); trimming it lets the loop then drop
      // the * and the dest-closing ) as well. A ] with balanced parens
      // (plain text, https://example.com/path]) is kept.
      let open = 0, close = 0;
      for (let k = 0; k < u.length; k++) { if (u[k] === '(') open++; else if (u[k] === ')') close++; }
      if (close > open) { u = u.slice(0, -1); continue; }
    }
    break;
  }
  return u;
}
// Greedy URL run: chars except whitespace and < ; a ( is included only if a
// ) occurs later in the same run (before whitespace/< /end). When
// stopAtBracket is set (a link bracket is open before the URL), a [ or ]
// ends the run: it is the link's own bracket, not part of the URL (marked's
// link token consumes it first, so the autolink never reaches it).
function greedyUrl(s, i, stopAtBracket) {
  const n = s.length;
  let j = i;
  while (j < n) {
    const c = s[j];
    if (c === ' ' || c === '\t' || c === '\n' || c === '<') break;
    if (stopAtBracket && (c === '[' || c === ']')) break;
    if (c === '(') {
      // find a ) later in this run
      let k = j + 1, ok = false;
      while (k < n) {
        const d = s[k];
        if (d === ' ' || d === '\t' || d === '\n' || d === '<') break;
        if (d === ')') { ok = true; break; }
        k++;
      }
      if (!ok) break;
    }
    j++;
  }
  return j;
}

// ---------------------------------------------------------------- inline parser

const WS_RE = /\s/;
const PUNCT_RE = /[\p{P}\p{S}]/u;
function isWS(c) { return c === undefined ? false : WS_RE.test(c); }
function isPunct(c) { return c !== undefined && PUNCT_RE.test(c); }

// Scan inline text into nodes. refs: Map of normalized label -> {dest, title}.
function tokenizeInline(s, refs) {
  const n = s.length;
  const nodes = [];
  let i = 0;
  let textStart = 0;
  // positions of unclosed [ / ![ openers, in scan order; a www/scheme
  // autolink ends before a ] that would close one of them, and the code
  // span scan below uses the same stack
  const openStack = [];
  const flushText = (end) => {
    if (end > textStart) nodes.push({ t: 'text', s: s.slice(textStart, end), pos: textStart, end });
  };
  while (i < n) {
    const c = s[i];
    // backslash
    if (c === '\\') {
      const d = s[i + 1];
      if (d === '\n') { flushText(i); nodes.push({ t: 'br', pos: i, end: i + 2 }); i += 2; while (i < n && (s[i] === ' ' || s[i] === '\t')) i++; textStart = i; continue; }
      if (d !== undefined && PUNCT.has(d)) { flushText(i); nodes.push({ t: 'text', s: d, pos: i, end: i + 2 }); i += 2; textStart = i; continue; }
      i++;
      continue;
    }
    // code span
    if (c === '`') {
      let j = i;
      while (j < n && s[j] === '`') j++;
      const run = j - i;
      // find matching run; the scan must not cross a ] that closes a
      // bracket opened BEFORE the code span when a link would form
      // there (marked's link regex claims that ] first, so no code
      // span may swallow it). A ] closing a bracket opened inside
      // the prospective code span does not block it (cm-537).
      // Backslashes are literal inside a code span: \` still closes
      // it (cm-338) — only \[ / \] are treated as escaped brackets.
      const isEscaped = (p) => {
        let b = 0;
        for (let q = p - 1; q >= 0 && s[q] === '\\'; q--) b++;
        return b % 2 === 1;
      };
      let k = j, found = -1, fend = -1, aborted = false;
      const baseDepth = openStack.length;
      let preScan = baseDepth; // pre-scan brackets still open
      const scanStack = openStack.slice();
      while (k < n) {
        if (s[k] === '`') {
          let m = k;
          while (m < n && s[m] === '`') m++;
          if (m - k === run) { found = k; fend = m; break; }
          k = m;
        } else if (s[k] === '[' && !isEscaped(k)) {
          const img = k > 0 && s[k - 1] === '!';
          scanStack.push({ pos: k, end: k + (img ? 2 : 1), image: img });
          k++;
        } else if (s[k] === ']' && !isEscaped(k)) {
          if (scanStack.length > preScan) {
            // closes a bracket opened inside the prospective code span
            scanStack.pop();
            k++;
          } else if (preScan > 0) {
            // closes the innermost pre-scan bracket: would a link form?
            const opener = scanStack[scanStack.length - 1];
            const label = s.slice(opener.end, k);
            let forms = false;
            if (labelTextValid(label)) {
              const after = k + 1;
              if (parseInlineLink(s, after)) forms = true;
              else {
                const rl = parseRefLabel(s, after);
                if (rl && rl.label !== '' && shortcutLabelValid(rl.label)) {
                  if (refs.get(normalizeLabel(rl.label))) forms = true;
                } else if (rl && rl.label === '' && shortcutLabelValid(label)) {
                  if (refs.get(normalizeLabel(label))) forms = true;
                } else if (!rl && shortcutLabelValid(label)) {
                  if (refs.get(normalizeLabel(label))) forms = true;
                }
              }
            }
            if (forms) { aborted = true; break; }
            scanStack.pop(); preScan--;
            k++;
          } else k++;
        } else k++;
      }
      if (aborted) { i = j; continue; }
      if (found !== -1) {
        flushText(i);
        let content = s.slice(j, found);
        content = content.replace(/\n/g, ' ');
        if (content.length >= 2 && content[0] === ' ' && content[content.length - 1] === ' ' && /[^ ]/.test(content)) {
          content = content.slice(1, -1);
        }
        nodes.push({ t: 'code', s: content, pos: i, end: fend });
        i = fend; textStart = i; continue;
      }
      i = j; continue;
    }
    // emphasis / strikethrough delimiters
    if (c === '*' || c === '_' || c === '~') {
      let j = i;
      while (j < n && s[j] === c) j++;
      let len = j - i;
      if (c === '~' && len >= 3) { i = j; continue; } // literal text
      const before = i > 0 ? s[i - 1] : undefined;
      const after = j < n ? s[j] : undefined;
      const beforeWS = i === 0 || isWS(before);
      const afterWS = j >= n || isWS(after);
      const beforeP = isPunct(before);
      const afterP = isPunct(after);
      const leftFlank = !afterWS && (!afterP || beforeWS || beforeP);
      const rightFlank = !beforeWS && (!beforeP || afterWS || afterP);
      let canOpen, canClose;
      if (c === '_') {
        canOpen = leftFlank && (!rightFlank || beforeP);
        canClose = rightFlank && (!leftFlank || afterP);
      } else {
        canOpen = leftFlank;
        canClose = rightFlank;
      }
      if (c === '~' && len > 2) len = 2; // runs >=3 are literal; len 2 max as delim
      if (canOpen || canClose) {
        flushText(i);
        nodes.push({ t: 'delim', ch: c, len, canOpen, canClose, active: true, used: 0, pos: i, end: j });
        i = j; textStart = i; continue;
      }
      i = j; continue;
    }
    // brackets / images
    if (c === '[' || (c === '!' && s[i + 1] === '[')) {
      const image = c === '!';
      flushText(i);
      nodes.push({ t: 'open', image, active: true, pos: i, end: i + (image ? 2 : 1) });
      openStack.push({ pos: i, end: i + (image ? 2 : 1), image });
      i += image ? 2 : 1; textStart = i; continue;
    }
    if (c === ']') {
      flushText(i);
      nodes.push({ t: 'close', pos: i, end: i + 1 });
      if (openStack.length) openStack.pop();
      i++; textStart = i; continue;
    }
    // raw html / autolink <
    if (c === '<') {
      const e = matchHtmlTag(s, i);
      if (e !== -1) { flushText(i); nodes.push({ t: 'html', s: s.slice(i, e), pos: i, end: e }); i = e; textStart = i; continue; }
      // autolink <scheme:...> or <email>
      const m = /^<([A-Za-z][A-Za-z0-9+.-]{1,31}:[^<>\s]*)>/.exec(s.slice(i, i + 200)) ||
                /^<([A-Za-z0-9.!#$%&'*+\/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?)+)>/.exec(s.slice(i, i + 200));
      if (m) {
        flushText(i);
        const raw = m[1];
        // an <email> autolink gets a mailto: href; a <scheme:...> one is used as-is
        const url = (raw.includes('@') && !raw.includes(':')) ? 'mailto:' + raw : raw;
        // angle-bracket autolinks survive inside link text (nested <a>);
        // only bare GFM extended autolinks are suppressed there
        nodes.push({ t: 'autolink', url, text: raw, angle: true, pos: i, end: i + m[0].length });
        i += m[0].length; textStart = i; continue;
      }
      i++;
      continue;
    }
    // hard break: 2+ spaces + newline (trailing spaces are consumed)
    if (c === ' ') {
      let j = i;
      while (s[j] === ' ') j++;
      if (j - i >= 2 && s[j] === '\n') { flushText(i); nodes.push({ t: 'br', pos: i, end: j + 1 }); i = j + 1; while (i < n && (s[i] === ' ' || s[i] === '\t')) i++; textStart = i; continue; }
    }
    // GFM extended autolinks: www. / scheme / email — only when not inside
    // a link text handled later; here we just detect at tokenize time.
    if (c === 'w' && s.startsWith('www.', i)) {
      const prev = i > 0 ? s[i - 1] : undefined;
      const okPrev = prev === undefined || isWS(prev) || prev === '(' || prev === '*' || prev === '_' || prev === '~';
      if (okPrev) {
        const end = greedyUrl(s, i, openStack.length > 0);
        if (end > i + 4) {
          const first = s.slice(i + 4, end);
          if (/^[A-Za-z0-9-]+(\.[A-Za-z0-9-]*)*/.test(first) && !first.startsWith('.') && !first.startsWith('_') && !first.startsWith('/') && first[0] !== '.') {
            const raw = s.slice(i, end);
            // no ]( cut: a standalone www.…](x) keeps ](x) in the URL;
            // inside link text the bracket-aware greedyUrl already
            // stops before the closing ]
            let u = raw;
            u = trimExtendedUrl(u);
            if (u.length > 4) { flushText(i); nodes.push({ t: 'autolink', url: 'http://' + u, text: u, pos: i, end: i + u.length }); i += u.length; textStart = i; continue; }
          }
        }
      }
    }
    if ((c === 'h' || c === 'H' || c === 'f' || c === 'F') && /^(?:https?|ftp):\/\//i.test(s.slice(i, i + 8))) {
      const m = /^(?:https?|ftp):\/\//i.exec(s.slice(i, i + 8));
      const end = greedyUrl(s, i, openStack.length > 0);
      const afterPrefix = s.slice(i + m[0].length, end);
      if (/^[A-Za-z0-9-]+(\.[A-Za-z0-9-]*)*/.test(afterPrefix) && afterPrefix[0] !== '.' && afterPrefix[0] !== '_' && afterPrefix[0] !== '/') {
        const raw = s.slice(i, end);
        let u = raw;
        u = trimExtendedUrl(u);
        if (u.length > m[0].length) { flushText(i); nodes.push({ t: 'autolink', url: u, text: u, pos: i, end: i + u.length }); i += u.length; textStart = i; continue; }
      }
    }
    // email (bare, not in < >) — only try at the start of a word run;
    // a __ immediately before is emphasis, not part of the word
    const prevIsWord = i > 0 && /[A-Za-z0-9._+\-]/.test(s[i - 1]) && !(s[i - 1] === '_' && i >= 2 && s[i - 2] === '_');
    if (/[A-Za-z0-9._+\-]/.test(c) && !prevIsWord) {
      const atIdx = s.indexOf('@', i);
      if (atIdx !== -1 && atIdx - i < 200) {
        const m = /^[A-Za-z0-9._+\-]+@[A-Za-z0-9_-]+(?:\.[A-Za-z0-9_-]+)*\.[A-Za-z0-9_-]*[A-Za-z0-9]/.exec(s.slice(i, i + 300));
        if (m) {
          let email = m[0];
          // backtrack: while the char after the match is a label char, drop
          // the last .label and re-check (foo@bar.com.a- -> foo@bar.com,
          // foo@bar.com- -> no match).
          let valid = true;
          // A trailing _ after the email is the emphasis closer, not
          // part of the domain, only when an unmatched _ opener is
          // still open: the nearest _ delimiter before the email must
          // itself be an opener (a closer after it means that opener
          // already closed, and a lone trailing _ kills the link).
          // (doc-25/31/34/37/38: __...email__ / _...email_)
          const trailingUnderscoreCloses = () => {
            for (let k = nodes.length - 1; k >= 0; k--) {
              const nd = nodes[k];
              if (nd.t === 'delim' && nd.ch === '_') return nd.canOpen === true;
            }
            return false;
          };
          while (true) {
            const after = s[i + email.length];
            if (after === undefined || !/[A-Za-z0-9_-]/.test(after)) break;
            if (after === '_' && trailingUnderscoreCloses()) break;
            const cut = email.lastIndexOf('.');
            const at = email.indexOf('@');
            if (cut <= at) { valid = false; break; }
            email = email.slice(0, cut);
          }
          if (valid && email.indexOf('.', email.indexOf('@')) !== -1) {
            // scheme prefix? mailto: / xmpp: immediately before
            let start = i, prefix = '';
            const pre = s.slice(Math.max(0, i - 12), i);
            const pm = /(?:(mailto|xmpp):)$/.exec(pre);
            if (pm) { start = i - pm[1].length - 1; prefix = pm[1] + ':'; }
            // xmpp path: /word after email
            let url = email, adv = email.length;
            if (prefix === 'xmpp:') {
              const pathM = /^\/[A-Za-z0-9_@.-]+/.exec(s.slice(i + email.length));
              if (pathM) { url += pathM[0]; adv += pathM[0].length; }
            }
            flushText(start);
            nodes.push({ t: 'autolink', url: prefix ? prefix + url : 'mailto:' + url, text: prefix + url, pos: start, end: i + adv });
            i += adv; textStart = i; continue;
          }
        }
      }
    }
    i++;
  }
  flushText(n);
  return nodes;
}

// ---------------------------------------------------------------- inline tree building

// Parse an inline link destination/title starting at s[i] (just after ']').
// Returns {dest, title, end} or null. dest/title are raw (unescaped) strings.
// marked's link-label pattern (re): the raw text between [ and ] must be a
// sequence of nested [...] groups (one level deep), backslash escapes,
// code-span-like units (a backtick run, non-backtick chars, a backtick
// run), a run of 2+ backticks immediately before the closing ], or any
// char except [ ] \ `. A stray ] or an unmatched backtick makes the
// label invalid and no link forms at this ].
function matchBracketGroup(text, i, allowNested) {
  // text[i] === '['; returns the index just past the matching ] or -1
  let j = i + 1;
  const n = text.length;
  while (j < n) {
    const d = text[j];
    if (d === '\\') { j += 2; continue; }
    if (d === ']') return j + 1;
    if (d === '[') {
      if (!allowNested) return -1;
      const inner = matchBracketGroup(text, j, false);
      if (inner === -1) return -1;
      j = inner; continue;
    }
    j++;
  }
  return -1;
}
function labelTextValid(text) {
  let i = 0;
  const n = text.length;
  while (i < n) {
    const c = text[i];
    if (c === '\\') { if (i + 1 >= n) return false; i += 2; continue; }
    if (c === '[') {
      const end = matchBracketGroup(text, i, true);
      if (end === -1) return false;
      i = end; continue;
    }
    if (c === '`') {
      let j = i;
      while (j < n && text[j] === '`') j++;
      const run = j - i;
      // a closing backtick run anywhere later?
      let k = j;
      while (k < n && text[k] !== '`') k++;
      if (k < n) {
        let m = k;
        while (m < n && text[m] === '`') m++;
        i = m; continue;
      }
      // no closing run: valid only as 2+ backticks at the very end
      if (run >= 2 && j === n) { i = j; continue; }
      return false;
    }
    if (c === ']') return false;
    i++;
  }
  return true;
}
// marked's shortcut/collapsed reference label (le): no unescaped [ or ],
// no newline followed by a blank line, not whitespace-only
function shortcutLabelValid(text) {
  if (!text || !/\S/.test(text)) return false;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (c === '\\') { i++; continue; }
    if (c === '[' || c === ']') return false;
    if (c === '\n') {
      let j = i + 1;
      while (j < text.length && (text[j] === ' ' || text[j] === '\t')) j++;
      if (j >= text.length || text[j] === '\n') return false;
    }
  }
  return true;
}

function parseInlineLink(s, i) {
  const n = s.length;
  if (s[i] !== '(') return null;
  let j = i + 1;
  while (j < n && (s[j] === ' ' || s[j] === '\t' || s[j] === '\n')) j++;
  if (j >= n) return null;
  let dest = '';
  if (s[j] === '<') {
    j++;
    const start = j;
    while (j < n && s[j] !== '>' && s[j] !== '\n') {
      if (s[j] === '\\' && j + 1 < n && PUNCT.has(s[j + 1])) j += 2;
      else if (s[j] === '<') return null;
      else j++;
    }
    if (j >= n || s[j] !== '>') return null;
    dest = s.slice(start, j);
    j++;
  } else {
    // bare dest: no spaces/control, balanced parens, backslash escapes
    let depth = 0;
    const start = j;
    while (j < n) {
      const c = s[j];
      if (c === ' ' || c === '\t' || c === '\n' || c < ' ') break;
      if (c === '\\' && j + 1 < n && PUNCT.has(s[j + 1])) { j += 2; continue; }
      if (c === '(') { depth++; j++; continue; }
      if (c === ')') {
        if (depth === 0) break;
        depth--; j++; continue;
      }
      j++;
    }
    dest = s.slice(start, j);
    // empty dest is valid: [link]() -> href="" (title may follow)
  }
  // unescape backslashes in dest
  dest = dest.replace(/\\([!"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~])/g, '$1');
  let title = null;
  // optional whitespace then optional title then optional whitespace then )
  let k = j;
  while (k < n && (s[k] === ' ' || s[k] === '\t' || s[k] === '\n')) k++;
  if (k < n && (s[k] === '"' || s[k] === "'" || s[k] === '(')) {
    const q = s[k];
    const closeQ = q === '(' ? ')' : q;
    let m = k + 1;
    const tstart = m;
    let ok = false;
    while (m < n) {
      if (s[m] === '\\' && m + 1 < n && PUNCT.has(s[m + 1])) { m += 2; continue; }
      if (s[m] === closeQ) { ok = true; break; }
      if (q === '(' && (s[m] === '(' || s[m] === ')')) break;
      m++;
    }
    if (!ok) return null;
    title = s.slice(tstart, m);
    title = title.replace(/\\([!"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~])/g, '$1');
    k = m + 1;
    while (k < n && (s[k] === ' ' || s[k] === '\t' || s[k] === '\n')) k++;
  }
  if (k >= n || s[k] !== ')') return null;
  return { dest, title, end: k + 1 };
}

// Parse a reference label starting at s[i] == '['. Returns {label, end} or null.
function parseRefLabel(s, i) {
  const n = s.length;
  if (s[i] !== '[') return null;
  let depth = 0, j = i + 1;
  while (j < n) {
    const c = s[j];
    if (c === '\\' && j + 1 < n && PUNCT.has(s[j + 1])) { j += 2; continue; }
    if (c === '[') { depth++; j++; continue; }
    if (c === ']') {
      if (depth === 0) return { label: s.slice(i + 1, j), end: j + 1 };
      depth--; j++; continue;
    }
    j++;
  }
  return null;
}

function normalizeLabel(label) {
  // only \[, \] and \\ are unescaped in a label (bracket chars and the
  // escape char itself); other backslash escapes stay literal, so
  // foo\! does NOT match foo! (cm-545), while ref\[ does match ref\[
  // (cm-549) and bar\\ matches bar\ (cm-550). Unicode casefold:
  // ẞ/ß fold to ss (cm-540).
  return label.replace(/\\([\[\]\\])/g, '$1').replace(/\s+/g, ' ').trim().toLowerCase().replace(/ß/g, 'ss').replace(/ẞ/g, 'ss');
}

// Plain text of a node list (for image alt and reference labels).
function plainTextOf(first, last) {
  let out = '';
  let cur = first;
  while (cur && cur !== last) {
    if (cur.t === 'text' || cur.t === 'code' || cur.t === 'html') out += cur.s;
    else if (cur.t === 'delim') out += cur.ch.repeat(cur.numDelims);
    else if (cur.t === 'open') out += cur.image ? '![' : '[';
    else if (cur.t === 'close') out += ']';
    else if (cur.t === 'autolink') out += cur.text;
    else if (cur.t === 'br') { /* contributes nothing */ }
    else if (cur.t === 'image') out += cur.alt; // nested image: its alt text
    else if (cur.t === 'link' || cur.t === 'em' || cur.t === 'strong' || cur.t === 'del') {
      out += plainTextOf(cur.childHead, null);
    }
    cur = cur.next;
  }
  return out;
}

// Remove a node from the top-level linked list.
function unlink(node) {
  if (node.prev) node.prev.next = node.next;
  if (node.next) node.next.prev = node.prev;
  node.next = node.prev = null;
  node.removed = true;
}
// Insert newNode before ref (top-level list).
function insertBefore(newNode, ref) {
  newNode.prev = ref.prev;
  newNode.next = ref;
  if (ref.prev) ref.prev.next = newNode;
  ref.prev = newNode;
  return newNode;
}

// Autolinks do not form inside link text: a bare URL inside [...] is
// plain text (nested <a> is invalid). Convert autolink nodes to text
// nodes, recursing into emphasis/strong/del/link children.
function stripAutolinks(first) {
  let cur = first;
  while (cur) {
    if (cur.t === 'autolink' && !cur.angle) {
      cur.t = 'text';
      cur.s = cur.text;
      cur.url = undefined;
    } else if (cur.childHead) {
      stripAutolinks(cur.childHead);
    }
    cur = cur.next;
  }
}

// Build the inline tree from tokenized nodes. s = source string, refs = Map.
// Returns the head node of the top-level list.
// Innermost still-open bracket at position pos (walking the node list
// from head): pushes [ / ![ nodes, pops on ] nodes.
function innermostOpenBracket(head, pos) {
  const stack = [];
  for (let cur = head; cur && cur.pos < pos; cur = cur.next) {
    if (cur.t === 'open' && !cur.removed) stack.push(cur);
    else if (cur.t === 'close' && !cur.removed && stack.length) stack.pop();
  }
  return stack.length ? stack[stack.length - 1] : null;
}

// Does bracket B (an open node) form a link? Find its closing ] by
// depth-counting from fromPos, then check for ( / [ / a defined shortcut
// ref. Returns the index of the closing ] or null.
function bracketWillLinkFrom(B, fromPos, s, refs) {
  let depth = 1, k = fromPos;
  while (k < s.length) {
    if (s[k] === '\\' && k + 1 < s.length) { k += 2; continue; }
    if (s[k] === '[') depth++;
    else if (s[k] === ']') { depth--; if (depth === 0) break; }
    k++;
  }
  if (depth !== 0) return null;
  const after = s[k + 1];
  if (after === '(' || after === '[') return k;
  const label = s.slice(B.end, k);
  if (refs.has(normalizeLabel(label))) return k;
  return null;
}

// marked's emStrong closer scan, over the delim nodes after opener op:
// a nested opener-like run raises the delimiter requirement (m), a
// both-flanking closer that violates the rule of 3 is skipped (f), and
// a closer must cover m. Returns true if some closer covers m.
// (e.g. *a **b**c* fails: the ** after b is both-flanking with
// y=1,b=2 so (1+2)%3==0, it is skipped, and the final * cannot cover
// m=3 — the outer * stays literal in marked.)
// The scan is tried for every suffix of the opener run: marked tries
// emStrong at each position inside a run, so **foo* can still pair
// using the second * (k=1, y=2) even though the whole run (k=2) cannot.
// o is set for suffixes: the char before the suffix is the same delim,
// so a both-flanking candidate breaks the scan there.
function openerCanPair(op, head, s, refs) {
  const len = op.numDelims;
  const before = op.pos > 0 ? s[op.pos - 1] : undefined;
  const afterOp = op.end < s.length ? s[op.end] : undefined;
  const pNonSpace = before !== undefined && !isWS(before);
  const h = before === '*' || before === '_' || isPunct(before);
  const d = isPunct(afterOp);
  const R = pNonSpace && (d || (op.ch === '*' && !h));
  // an opener inside a link's text cannot pair past that link's ]
  const bOpen = innermostOpenBracket(head, op.pos);
  let bOpenClose = -1;
  if (bOpen && bOpen.pos < op.pos) {
    const c = bracketWillLinkFrom(bOpen, op.pos, s, refs);
    if (c !== null) bOpenClose = c;
  }
  for (let offset = 0; offset < len; offset++) {
    const k = len - offset;
    const y = len;
    const o = offset > 0;
    let m = k, f = 0;
    let firstStar = true;
    let ok = false;
    for (let cur = op.next; cur; cur = cur.next) {
      if (cur.t !== 'delim' || cur.ch !== op.ch || cur.removed || cur.parent) continue;
      if (cur.numDelims <= 0) continue;
      if (bOpenClose !== -1 && cur.pos > bOpenClose) continue;
      // marked's closer regex first alternative skips a single * that
      // sits between a __ pair at the start of the scan
      // (^[^_*]*?__[^_*]*?\*[^_*]*?(?=__))
      if (firstStar) {
        firstStar = false;
        const pre = s.slice(op.end, cur.pos);
        if (/^[^_*]*?__[^_*]*?$/.test(pre) && /^[^_*]*?__/.test(s.slice(cur.end))) continue;
      }
      // a closer inside a to-be-link bracket is invisible to an opener
      // outside that bracket
      const b = innermostOpenBracket(head, cur.pos);
      if (b && b.pos > op.pos && bracketWillLinkFrom(b, cur.pos, s, refs) !== null) continue;
      const blen = cur.numDelims;
      if (cur.canOpen && !cur.canClose) { m += blen; continue; }
      if (cur.canOpen && cur.canClose) {
        if (o) break; // previous char is the same delim: stop the scan
        if (y % 3 !== 0 && (y + blen) % 3 === 0) { f += blen; continue; }
      } else if (R) {
        if (y % 3 !== 0 && (y + blen) % 3 === 0) { f += blen; continue; }
      }
      m -= blen;
      if (m > 0) continue;
      ok = true;
      break;
    }
    if (ok) return true;
  }
  return false;
}

// Pre-pass: a * opener whose closer scan cannot cover the delimiter
// requirement can never pair in marked's model — mark it dead so the
// stack resolver does not pair it either. Runs before the main loop;
// only sets a dead flag, never changes canOpen/canClose (the stack's
// rule-of-3 check depends on them) or list structure.
function markDeadStarOpeners(head, s, refs) {
  for (let cur = head; cur; cur = cur.next) {
    if (cur.t === 'delim' && cur.ch === '*' && cur.canOpen && cur.numDelims > 0) {
      if (!openerCanPair(cur, head, s, refs)) cur.dead = true;
    }
  }
}

function buildInlineTree(s, refs) {
  const nodes = tokenizeInline(s, refs);
  if (nodes.length === 0) return null;
  for (let i = 0; i < nodes.length; i++) {
    nodes[i].next = nodes[i + 1] || null;
    nodes[i].prev = nodes[i - 1] || null;
    nodes[i].parent = null;
    nodes[i].removed = false;
    if (nodes[i].t === 'delim') nodes[i].numDelims = nodes[i].len;
  }
  let head = nodes[0];
  markDeadStarOpeners(head, s, refs);
  const delimStack = [];
  const bracketStack = [];
  let cur = head;
  while (cur) {
    const next = cur.next;
    if (cur.removed || cur.parent) { cur = next; continue; }
    if (cur.t === 'delim') {
      // try to close
      if (cur.canClose && cur.numDelims > 0) {
        // innermost still-open bracket before this closer: openers at or
        // before it are outside the bracket pair and cannot match a
        // closer inside it -- but ONLY if that bracket will actually
        // form a link (e.g. *[bar*](/url)); if it will not (e.g.
        // *foo [bar* baz]), the delimiters may still pair (cm-523)
        let bracketPos = -1, bracketNode = null;
        for (const b of bracketStack) {
          if (!b.removed && !b.parent && b.active && b.pos < cur.pos && b.pos > bracketPos) { bracketPos = b.pos; bracketNode = b; }
        }
        let bracketWillLink = false;
        if (bracketNode) {
          // find the ] closing this bracket (depth counting, \-aware)
          let depth = 1, k = cur.pos;
          while (k < s.length) {
            if (s[k] === '\\' && k + 1 < s.length) { k += 2; continue; }
            if (s[k] === '[') depth++;
            else if (s[k] === ']') { depth--; if (depth === 0) break; }
            k++;
          }
          if (depth === 0) {
            const after = s[k + 1];
            if (after === '(' || after === '[') bracketWillLink = true;
            else {
              // shortcut reference? label = raw text between [ and ]
              const label = s.slice(bracketNode.end, k);
              if (refs.has(normalizeLabel(label))) bracketWillLink = true;
            }
          }
        }
        if (!bracketWillLink) bracketPos = -1;
        while (cur.numDelims > 0 && !cur.removed) {
          let opener = null, oi = -1;
          for (let k = delimStack.length - 1; k >= 0; k--) {
            const o = delimStack[k];
            if (o.removed || o.parent || o.dead || o.numDelims <= 0 || !o.canOpen || o.ch !== cur.ch) continue;
            if (o.pos < bracketPos) continue;
            // rule of 3: applies if EITHER delimiter can both open and close
            if (((o.canOpen && o.canClose) || (cur.canOpen && cur.canClose)) &&
              (o.numDelims + cur.numDelims) % 3 === 0 &&
              (o.numDelims % 3 !== 0 || cur.numDelims % 3 !== 0)) continue;
            opener = o; oi = k; break;
          }
          if (!opener) break;
          const isDel = cur.ch === '~';
          const use = isDel ? Math.min(opener.numDelims, cur.numDelims)
            : (opener.numDelims >= 2 && cur.numDelims >= 2) ? 2 : 1;
          const tag = isDel ? 'del' : use === 2 ? 'strong' : 'em';
          const emNode = { t: tag, ch: cur.ch, pos: opener.pos, end: cur.end, next: null, prev: null, parent: null, removed: false, childHead: null };
          // collect children between opener and closer
          let childHead = opener.next, childTail = null;
          let c = opener.next;
          while (c && c !== cur) { childTail = c; c = c.next; }
          if (childHead && childHead !== cur) {
            emNode.childHead = childHead;
            if (childHead.prev) childHead.prev.next = null;
            childHead.prev = null;
            if (childTail) childTail.next = null;
            let cc = childHead;
            while (cc) { cc.parent = emNode; cc = cc.next; }
          }
          // insert emNode between opener and closer
          emNode.prev = opener;
          emNode.next = cur;
          opener.next = emNode;
          cur.prev = emNode;
          opener.numDelims -= use;
          cur.numDelims -= use;
          if (opener.numDelims === 0) {
            unlink(opener);
            if (head === opener) head = emNode;
            delimStack.splice(oi, 1);
          }
          if (cur.numDelims === 0) {
            const nx = cur.next;
            unlink(cur);
            cur = null;
            break;
          }
          // closer still has delims: keep looking (it may match again)
        }
        if (cur && cur.removed) { cur = next; continue; }
        if (cur && !cur.removed && cur.canOpen && !cur.dead && cur.numDelims > 0) delimStack.push(cur);
        cur = next;
        continue;
      }
      if (!cur.removed && cur.canOpen && !cur.dead && cur.numDelims > 0) delimStack.push(cur);
    } else if (cur.t === 'open') {
      bracketStack.push(cur);
    } else if (cur.t === 'close') {
      // take the TOP opener (most recent), not the nearest active one:
      // if it is inactive (a link formed inside it), this ] is literal
      // and must NOT pair with an earlier opener (cm-520); pop it.
      let oi = -1, opener = null;
      for (let k = bracketStack.length - 1; k >= 0; k--) {
        const o = bracketStack[k];
        if (!o.removed && !o.parent) { opener = o; oi = k; break; }
      }
      if (opener && !opener.active) {
        bracketStack.splice(oi, 1);
        opener = null;
      }
      if (opener) {
        // try inline link
        const after = cur.end;
        let link = null, linkEnd = -1;
        const text = s.slice(opener.end, cur.pos);
        const il = labelTextValid(text) ? parseInlineLink(s, after) : null;
        if (il) { link = il; linkEnd = il.end; }
        else {
          const rl = parseRefLabel(s, after);
          // full ref: marked's reflink needs a valid link text (re) and
          // a valid ref label (le); a syntactically valid but undefined
          // ref leaves the [ literal — no shortcut fall-through
          const fullOk = rl && rl.label !== '' && labelTextValid(text) && shortcutLabelValid(rl.label);
          if (fullOk) {
            const ref = refs.get(normalizeLabel(rl.label));
            if (ref) { link = { dest: ref.dest, title: ref.title }; linkEnd = rl.end; }
          } else if (rl && rl.label === '' && shortcutLabelValid(text)) {
            // collapsed ref: the text itself is the label
            const ref = refs.get(normalizeLabel(text));
            if (ref) { link = { dest: ref.dest, title: ref.title }; linkEnd = rl.end; }
          } else if (!fullOk) {
            // shortcut ref, only when no valid full/collapsed form claimed it
            const ref = shortcutLabelValid(text) ? refs.get(normalizeLabel(text)) : undefined;
            if (ref) { link = { dest: ref.dest, title: ref.title }; linkEnd = after; }
          }
        }
        if (link) {
          const isImage = opener.image;
          const linkNode = isImage
            ? { t: 'image', dest: link.dest, title: link.title, alt: '', pos: opener.pos, end: linkEnd, next: null, prev: null, parent: null, removed: false, childHead: null }
            : { t: 'link', dest: link.dest, title: link.title, pos: opener.pos, end: linkEnd, next: null, prev: null, parent: null, removed: false, childHead: null };
          // children between opener and closer
          let childHead = opener.next, childTail = null;
          let c = opener.next;
          while (c && c !== cur) { childTail = c; c = c.next; }
          if (isImage) {
            linkNode.alt = plainTextOf(childHead, cur);
            // drop children (alt is plain text)
            let cc = childHead;
            while (cc && cc !== cur) { const nx = cc.next; cc.next = cc.prev = null; cc.removed = true; cc = nx; }
          } else if (childHead && childHead !== cur) {
            linkNode.childHead = childHead;
            if (childHead.prev) childHead.prev.next = null;
            childHead.prev = null;
            if (childTail) childTail.next = null;
            // strip after severing childTail.next so the walk stays
            // inside the link text and cannot reach later autolinks
            stripAutolinks(childHead);
            let cc = childHead;
            while (cc) { cc.parent = linkNode; cc = cc.next; }
          }
          // Find the first node at/after linkEnd, splitting a text node.
          // Nodes before it (the link suffix) are marked removed and bypassed.
          let suffixEnd = cur.next;
          let sn = cur.next;
          while (sn && sn.pos < linkEnd) {
            const nx = sn.next;
            if (sn.t === 'text' && sn.end > linkEnd) {
              sn.s = sn.s.slice(linkEnd - sn.pos);
              sn.pos = linkEnd;
              suffixEnd = sn;
              break;
            }
            sn.removed = true;
            sn = nx;
            suffixEnd = sn;
          }
          // insert linkNode in place of opener..cur, next = suffixEnd
          linkNode.prev = opener.prev;
          linkNode.next = suffixEnd;
          if (opener.prev) opener.prev.next = linkNode;
          if (suffixEnd) suffixEnd.prev = linkNode;
          if (head === opener) head = linkNode;
          opener.next = opener.prev = null; opener.removed = true;
          cur.next = cur.prev = null; cur.removed = true;
          bracketStack.splice(oi, 1);
          if (!isImage) {
            // a link deactivates remaining LINK openers (no nested
            // links) but NOT image openers: an image can still form
            // around a link, using the link as alt text (cm-520)
            for (const b of bracketStack) if (!b.image) b.active = false;
          }
        } else {
          // no link formed: remove this opener from the stack so a
          // later ] can pair with an earlier one ([a [b]](/u) uses [a)
          bracketStack.splice(oi, 1);
        }
      }
    }
    cur = next;
  }
  return head;
}

// Render an inline node list to HTML.
function renderInlineList(head) {
  let out = '';
  let cur = head;
  while (cur) {
    switch (cur.t) {
      case 'text': out += escText(decodeNumericRefs(cur.s)); break;
      case 'code': out += '<code>' + escEncode(cur.s) + '</code>'; break;
      case 'html': out += cur.s; break;
      case 'br': out += '<br>'; break;
      case 'delim': out += escText(cur.ch.repeat(cur.numDelims)); break;
      case 'open': out += cur.image ? '![' : '['; break;
      case 'close': out += ']'; break;
      case 'autolink': {
        const href = escAttr(cleanUrl(cur.url) ?? cur.url);
        out += '<a href="' + href + '">' + escText(cur.text) + '</a>';
        break;
      }
      case 'link': {
        const href = escAttr(cleanUrl(cur.dest) ?? cur.dest);
        out += '<a href="' + href + '"';
        if (cur.title !== null && cur.title !== undefined) out += ' title="' + escAttr(cur.title) + '"';
        out += '>' + renderInlineList(cur.childHead) + '</a>';
        break;
      }
      case 'image': {
        const src = escAttr(cleanUrl(cur.dest) ?? cur.dest);
        out += '<img src="' + src + '" alt="' + escAttr(decodeNumericRefs(cur.alt)) + '"';
        if (cur.title !== null && cur.title !== undefined) out += ' title="' + escAttr(cur.title) + '"';
        out += '>';
        break;
      }
      case 'em': out += '<em>' + renderInlineList(cur.childHead) + '</em>'; break;
      case 'strong': out += '<strong>' + renderInlineList(cur.childHead) + '</strong>'; break;
      case 'del': out += '<del>' + renderInlineList(cur.childHead) + '</del>'; break;
    }
    cur = cur.next;
  }
  return out;
}

function parseInline(s, refs) {
  if (s === '') return '';
  return renderInlineList(buildInlineTree(s, refs));
}

// ---------------------------------------------------------------- block parser
// Line-based container parser. Lines carry a `lazy` flag (true when the line
// did not match the current container's markers — only meaningful for the
// table rule inside blockquotes).

function splitLines(src) {
  const lines = [];
  let start = 0;
  for (let i = 0; i < src.length; i++) {
    if (src[i] === '\n') {
      lines.push({ text: src.slice(start, i), lazy: false, col: 0, blank: /^[ \t]*$/.test(src.slice(start, i)) });
      start = i + 1;
    }
  }
  if (start < src.length) lines.push({ text: src.slice(start), lazy: false, col: 0, blank: /^[ \t]*$/.test(src.slice(start)) });
  return lines;
}
function isBlankLine(t) { return /^[ \t]*$/.test(t); }
function indentOf(t, startCol) {
  let n = startCol || 0;
  let i = 0;
  for (; i < t.length; i++) {
    if (t[i] === ' ') n++;
    else if (t[i] === '\t') n += 4 - (n % 4);
    else break;
  }
  return n - (startCol || 0);
}
// Expand the tabs in a leading run of spaces/tabs to spaces, tracking
// columns from `startCol` (marked's J helper: a tab advances to the next
// multiple of 4). Only the leading whitespace run is touched.
function expandLeadingTabs(s, startCol) {
  let col = startCol || 0, i = 0;
  let out = '';
  while (i < s.length && (s[i] === ' ' || s[i] === '\t')) {
    if (s[i] === ' ') { out += ' '; col++; i++; }
    else { const adv = 4 - (col % 4); out += ' '.repeat(adv); col += adv; i++; }
  }
  return out + s.slice(i);
}
// Fenced-code dedent (marked's Dt): remove up to `n` leading-whitespace
// CHARACTERS from a content line, where n is the opening fence line's
// leading-whitespace length. A tab counts as one character.
function fenceDedent(line, n) {
  if (n <= 0) return line;
  let i = 0;
  while (i < line.length && i < n && (line[i] === ' ' || line[i] === '\t')) i++;
  return line.slice(i);
}
// Indented-code dedent (marked's codeRemoveIndent): remove 1-4 leading
// spaces, or 0-3 spaces followed by a tab (the tab is removed, not expanded).
function indentedCodeDedent(line) {
  const m = /^(?: {0,3}\t| {1,4})/.exec(line);
  return m ? line.slice(m[0].length) : line;
}

// column-aware: strip up to `count` columns of indent from the start of t,
// where t starts at absolute column startCol. Returns {rest, newCol}.
function stripIndent(t, count, startCol) {
  let col = startCol || 0, i = 0;
  const target = col + count;
  while (i < t.length && col < target) {
    const c = t[i];
    if (c === ' ') { col++; i++; }
    else if (c === '\t') {
      const adv = 4 - (col % 4);
      if (col + adv <= target) { col += adv; i++; }
      else {
        const remaining = target - col;
        return { rest: ' '.repeat(adv - remaining) + t.slice(i + 1), newCol: target };
      }
    } else break;
  }
  // a tab starting exactly at the strip boundary is expanded to spaces
  // (its advance to the next tab stop belongs to the content, e.g. a
  // tab at col 8 after stripping 8 columns becomes 4 spaces, doc-01)
  if (i < t.length && t[i] === '\t' && col === target) {
    const adv = 4 - (col % 4);
    return { rest: ' '.repeat(adv) + t.slice(i + 1), newCol: col + adv };
  }
  return { rest: t.slice(i), newCol: col };
}
// Strip a blockquote marker (> + optional space/tab) from t (starting at
// absolute column startCol). Returns {content, newCol} or null.
// Marked's rule: the whitespace after `>` is tab-expanded (columns from
// just after `>`), then the marker plus one space is removed — so
// `> \tfoo` yields two spaces, `>\tfoo` yields two spaces, `>  \tfoo`
// yields two spaces.
function stripBlockquoteMarker(t, startCol) {
  let col = startCol || 0, i = 0;
  while (i < t.length && t[i] === ' ' && col - (startCol || 0) < 3) { i++; col++; }
  if (i >= t.length || t[i] !== '>') return null;
  i++; col++;
  // whitespace run after `>`: expand its tabs, then drop one space.
  // The expansion base is the marker's length WITHIN this text (the
  // leading spaces + `>`), not the absolute column: marked re-lexes
  // container-stripped text fresh, so a tab after `>` in `> \t...`
  // expands from column 1 (doc-05/09/17/36: 2 spaces, not 4).
  let j = i;
  while (j < t.length && (t[j] === ' ' || t[j] === '\t')) j++;
  if (j === i) return { content: t.slice(i), newCol: col };
  const expanded = expandLeadingTabs(t.slice(i), i);
  // expanded starts with the run as spaces; drop exactly one of them
  return { content: expanded.slice(1), newCol: col + 1 };
}

// ---- tables ----
function splitTableCells(line) {
  // split on unescaped | ; leading/trailing pipes stripped; cells trimmed
  const cells = [];
  let cur = '';
  let i = 0;
  const n = line.length;
  // strip leading pipe (after optional spaces)
  let s = line;
  const lead = /^ *\|/.exec(s);
  if (lead) s = s.slice(lead[0].length);
  const trail = /\| *$/.exec(s);
  if (trail) s = s.slice(0, s.length - trail[0].length);
  while (i < s.length) {
    const c = s[i];
    if (c === '\\' && i + 1 < s.length && s[i + 1] === '|') { cur += '|'; i += 2; continue; }
    if (c === '|') { cells.push(cur.trim()); cur = ''; i++; continue; }
    cur += c; i++;
  }
  cells.push(cur.trim());
  return cells;
}
function parseDelimiterRow(line) {
  // returns array of alignments ('left'|'right'|'center'|null) or null
  // (delimiter row must have at most 3 spaces of indent)
  if (indentOf(line, 0) > 3) return null;
  const cells = splitTableCells(line);
  if (cells.length === 0) return null;
  const align = [];
  for (const cell of cells) {
    const m = /^(:?)-+(:?)$/.exec(cell);
    if (!m) return null;
    if (m[1] === ':' && m[2] === ':') align.push('center');
    else if (m[1] === ':') align.push('left');
    else if (m[2] === ':') align.push('right');
    else align.push(null);
  }
  return align;
}
function isDelimiterRow(line) { return parseDelimiterRow(line) !== null; }

// ---- HTML blocks ----
const HTML_BLOCK_START = [
  { re: /^ {0,3}<(script|pre|style|textarea)([ \t>]|\/>|$)/i, end: /<\/(script|pre|style|textarea)>/i },
  { re: /^ {0,3}<!--/, end: /-->/ },
  { re: /^ {0,3}<\?/, end: /\?>/ },
  { re: /^ {0,3}<![A-Za-z]/, end: />/ },
  { re: /^ {0,3}<!\[CDATA\[/, end: /\]\]>/ },
];
// block tag names for type 6
const HTML_BLOCK_TAG_RE = /^ {0,3}<\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?:[ \t>]|\/>|$)/i;
// type 7: a complete open or close tag alone on the line
const HTML_TYPE7_OPEN_RE = /^ {0,3}<[A-Za-z][A-Za-z0-9-]*(?:[ \t]+[A-Za-z_:][A-Za-z0-9_.:-]*(?:[ \t]*=[ \t]*(?:"[^"]*"|'[^']*'|[^\s"'=<`>]+))?)*[ \t]*\/?>[ \t]*$/;
const HTML_TYPE7_CLOSE_RE = /^ {0,3}<\/[A-Za-z][A-Za-z0-9-]*[ \t]*>[ \t]*$/;

function htmlBlockStart(line) {
  for (let k = 0; k < HTML_BLOCK_START.length; k++) {
    if (HTML_BLOCK_START[k].re.test(line)) return { type: k + 1, endRe: HTML_BLOCK_START[k].end };
  }
  if (HTML_BLOCK_TAG_RE.test(line)) return { type: 6, endRe: null };
  // type 7: a complete open tag (with attributes) or close tag
  // (NO attributes: </a href="foo"> is not a tag, cm-624) alone on a line
  if (HTML_TYPE7_OPEN_RE.test(line) || HTML_TYPE7_CLOSE_RE.test(line)) return { type: 7, endRe: null };
  return null;
}

// ---- link reference definitions ----
function parseLinkDef(lines, startIdx) {
  // Try to parse a link ref def starting at lines[startIdx].
  // Returns {endIdx (exclusive), dest, title, label} or null.
  const n = lines.length;
  let li = startIdx;
  let t = lines[li].text;
  let pos = 0;
  let lead = 0;
  while (lead < t.length && t[lead] === ' ' && lead < 3) lead++;
  pos = lead;
  if (t[pos] !== '[') return null;
  pos++;
  // label (may span lines; only \[ and \] unescaped, matching normalizeLabel)
  let label = '';
  let closed = false;
  while (!closed) {
    while (pos < t.length) {
      const ch = t[pos];
      if (ch === '\\' && pos + 1 < t.length && (t[pos + 1] === '[' || t[pos + 1] === ']' || t[pos + 1] === '\\')) { label += t[pos + 1]; pos += 2; continue; }
      if (ch === '[') return null; // unescaped [ in a label: not a valid def
      if (ch === ']') { closed = true; pos++; break; }
      label += ch; pos++;
    }
    if (closed) break;
    li++;
    if (li >= n) return null;
    if (lines[li].blank) return null;
    t = lines[li].text; pos = 0;
    label += '\n';
  }
  const normLabel = normalizeLabel(label);
  if (normLabel === '' || label.length > 999) return null;
  // expect ':' (skip spaces; if at EOL, try the next line)
  while (pos < t.length && t[pos] === ' ') pos++;
  if (pos >= t.length) {
    li++;
    if (li >= n) return null;
    if (lines[li].blank) return null;
    t = lines[li].text; pos = 0;
    while (pos < t.length && t[pos] === ' ') pos++;
  }
  if (t[pos] !== ':') return null;
  pos++;
  // skip whitespace/newlines to the dest
  let destLine = -1;
  while (true) {
    while (pos < t.length && (t[pos] === ' ' || t[pos] === '\t')) pos++;
    if (pos < t.length) { destLine = li; break; }
    li++;
    if (li >= n) return null;
    if (lines[li].blank) return null;
    t = lines[li].text; pos = 0;
  }
  // dest
  let dest = '';
  if (t[pos] === '<') {
    pos++;
    let dEnd = -1;
    while (pos < t.length) {
      const ch = t[pos];
      if (ch === '>') { dEnd = pos; break; }
      if (ch === '<') return null;
      if (ch === '\\' && pos + 1 < t.length && PUNCT.has(t[pos + 1])) { dest += t[pos + 1]; pos += 2; continue; }
      dest += ch; pos++;
    }
    if (dEnd < 0) return null;
    pos = dEnd + 1;
  } else {
    let depth = 0, started = false;
    while (pos < t.length) {
      const ch = t[pos];
      if (ch === ' ' || ch === '\t') break;
      if (ch === '\\' && pos + 1 < t.length && PUNCT.has(t[pos + 1])) { dest += t[pos + 1]; pos += 2; started = true; continue; }
      if (ch === '(') { depth++; dest += ch; pos++; started = true; continue; }
      if (ch === ')') { if (depth === 0) break; depth--; dest += ch; pos++; started = true; continue; }
      if (ch < ' ') return null;
      dest += ch; pos++; started = true;
    }
    if (!started) return null;
    if (depth !== 0) return null;
  }
  // after dest: optional title, then only whitespace to end of line.
  // A title requires whitespace (or a line break) before it.
  let title = null, endIdx = destLine + 1;
  let hadSpace = false, crossedLine = false;
  while (true) {
    while (pos < t.length && (t[pos] === ' ' || t[pos] === '\t')) { pos++; hadSpace = true; }
    if (pos < t.length) break;
    li++;
    if (li >= n) return { label: normLabel, dest, title: null, endIdx: destLine + 1 };
    if (lines[li].blank) return { label: normLabel, dest, title: null, endIdx: destLine + 1 };
    t = lines[li].text; pos = 0; hadSpace = true; crossedLine = true;
  }
  if (!hadSpace) return null; // junk immediately after dest (e.g. <bar>(baz))
  const titleStartLine = li;
  const q = t[pos];
  if (q === '"' || q === "'" || q === '(') {
    const closeQ = q === '(' ? ')' : q;
    let titleText = '';
    pos++;
    let closedT = false, badParen = false;
    let closeLine = li, closePos = -1;
    while (true) {
      let stop = false;
      while (pos < t.length) {
        const ch = t[pos];
        if (ch === '\\' && pos + 1 < t.length && PUNCT.has(t[pos + 1])) { titleText += t[pos + 1]; pos += 2; continue; }
        if (ch === closeQ) { closedT = true; closeLine = li; closePos = pos; stop = true; break; }
        if (q === '(' && (ch === '(' || ch === ')')) { badParen = true; stop = true; break; }
        titleText += ch; pos++;
      }
      if (stop) break;
      li++;
      if (li >= n) return null;
      if (lines[li].blank) return null;
      titleText += '\n';
      t = lines[li].text; pos = 0;
    }
    if (badParen) return null;
    if (!closedT) return null;
    const after = t.slice(closePos + 1);
    if (/^[ \t]*$/.test(after)) {
      title = titleText;
      endIdx = closeLine + 1;
    } else {
      // junk after the title: title dropped; if it started on the dest line
      // the whole def is invalid; otherwise the title line is not consumed
      if (titleStartLine === destLine) return null;
      title = null;
      endIdx = destLine + 1;
    }
  } else {
    // not a title: on a following line the def simply ends (no title);
    // on the dest line it is junk, so the def is invalid
    if (crossedLine) return { label: normLabel, dest, title: null, endIdx: destLine + 1 };
    return null;
  }
  return { dest, title, endIdx, label: normLabel };
}

// ---------------------------------------------------------------- parseBlocks
// lines: [{text, lazy}]; refs: Map. Returns {blocks, loose}.
// blocks: [{type, ...}]. `loose` is true when a blank line separates blocks.

// Returns fence info {ch, len, info} or null. A backtick fence whose info
// string contains a backtick is NOT a fence.
function fenceInfo(t) {
  const fm = /^ {0,3}(`{3,}|~{3,})(.*)$/.exec(t);
  if (!fm) return null;
  const ch = fm[1][0];
  const info = fm[2].trim();
  if (ch === '`' && info.includes('`')) return null;
  return { ch, len: fm[1].length, info };
}

function parseBlocks(lines, refs, inListItem) {
  const blocks = [];
  let loose = false;
  let para = null; // {lines:[{text,lazy}], startIdx}
  let i = 0;
  const n = lines.length;

  const flushPara = () => {
    if (!para) return;
    const b = finalizeParagraph(para.lines, refs);
    if (b) {
      if (Array.isArray(b)) blocks.push(...b);
      else blocks.push(b);
    }
    para = null;
  };

  // check if line (at index idx) starts a block that can interrupt a paragraph
  // (ATX, fence, hr, html 1-6, blockquote, list that can interrupt)
  const blockStartKind = (idx, inPara) => {
    const t = lines[idx].text;
    if (/^ {0,3}#{1,6}(?:[ \t]+|$)/.test(t)) return 'atx';
    if (fenceInfo(t)) return 'fence';
    if (/^ {0,3}((?:\*[ \t]*){3,}|(?:-[ \t]*){3,}|(?:_[ \t]*){3,})[ \t]*$/.test(t)) return 'hr';
    const hb = htmlBlockStart(t);
    if (hb && (hb.type <= 6 || !inPara)) return 'html';
    if (/^ {0,3}>/.test(t)) return 'blockquote';
    const lm = /^ {0,3}([*+-]|\d{1,9}[.)])(?:[ \t]+|$)/.exec(t);
    if (lm) {
      // list interruption rules
      const after = t.slice(lm[0].length);
      const empty = /^[ \t]*$/.test(after);
      if (!inPara) return 'list';
      if (empty) return null;
      if (lm[1] === '*' || lm[1] === '+' || lm[1] === '-') return 'list';
      // ordered: only if start number is 1
      const num = parseInt(lm[1], 10);
      if (num === 1 || inListItem) return 'list';
      return null;
    }
    return null;
  };

  while (i < n) {
    const line = lines[i];
    const t = line.text;
    if (line.blank) {
      flushPara();
      i++;
      // blank line between blocks -> loose (if a block follows)
      let j = i;
      while (j < n && lines[j].blank) j++;
      if (j < n && blocks.length > 0) loose = true;
      continue;
    }
    // a whitespace-only line from a container strip only continues an open
    // paragraph; it never opens one (cm-240)
    if (!para && /^[ \t]*$/.test(t)) { i++; continue; }
    // a lazy continuation line never starts a block; it extends the paragraph
    if (line.lazy) {
      if (!para) para = { lines: [] };
      para.lines.push({ text: t, lazy: line.lazy, blank: false });
      i++;
      continue;
    }
    const inPara = para !== null;
    // setext / table checks when a paragraph is open
    if (inPara && !line.lazy) {
      // setext underline (must not be a lazy line)
      const sm = /^ {0,3}(=+|-+)[ \t]*$/.exec(t);
      if (sm) {
        const level = sm[1][0] === '=' ? 1 : 2;
        const remaining = extractLinkDefs(para.lines, refs);
        if (remaining.length > 0) {
          let text = remaining.map(l => l.text).join('\n');
          text = text.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
          para = null;
          blocks.push({ type: 'heading', level, text });
          i++;
          continue;
        }
        // paragraph was all link ref defs; the underline is not setext.
        para = null;
        continue; // re-process this line as a fresh line (i not advanced)
      }
      // table delimiter (mode A)
      if (isDelimiterRow(t)) {
        const align = parseDelimiterRow(t);
        const lastLine = para.lines[para.lines.length - 1];
        const headerCells = splitTableCells(lastLine.text);
        const lazyDelim = line.lazy;
        const lazyHeader = lastLine.lazy;
        const inBq = false; // laziness exception only applies in blockquotes;
        // we track it via the `lazy` flags + a flag on the line set (see below)
        const exception = lazyDelim && !lazyHeader && lines._inBlockquote;
        if (headerCells.length === align.length && !exception) {
          // split paragraph: earlier lines stay a paragraph, last line = header
          const earlier = para.lines.slice(0, -1);
          const savedPara = para;
          para = null;
          if (earlier.length > 0) {
            const b = finalizeParagraph(earlier, refs);
            if (b) { if (Array.isArray(b)) blocks.push(...b); else blocks.push(b); }
          }
          // consume delimiter + body rows
          const table = { type: 'table', align, header: headerCells, rows: [] };
          i++;
          while (i < n) {
            const bl = lines[i];
            // a line of only spaces ends the table, but a line holding a
            // tab is a row of empty cells (marked's table regex excludes
            // only ` *\n` lines from the body; doc-26/33)
            if (bl.blank && !bl.text.includes('\t')) break;
            if (blockStartKind(i, false)) break;
            table.rows.push(splitTableCells(bl.text));
            i++;
          }
          blocks.push(table);
          continue;
        }
        // else: delimiter is just a paragraph line
      }
      // paragraph-stop: if this line is a potential header and the NEXT line
      // is a delimiter row, end the paragraph before this line
      // (but not when the next line is a setext underline — setext wins)
      if (!isDelimiterRow(t) && i + 1 < n && isDelimiterRow(lines[i + 1].text) &&
        !/^ {0,3}(=+|-+)[ \t]*$/.test(lines[i + 1].text)) {
        const nextLazy = lines[i + 1].lazy;
        const exception = nextLazy && !line.lazy && lines._inBlockquote;
        if (!exception) {
          flushPara();
          continue; // re-process this line as a new block
        }
      }
    }
    // block starts
    const kind = blockStartKind(i, inPara);
    if (kind === 'atx' || kind === 'fence' || kind === 'hr' || kind === 'html' || kind === 'blockquote' || kind === 'list') {
      flushPara();
      if (kind === 'atx') {
        const m = /^ {0,3}(#{1,6})[ \t]*(.*?)[ \t]*$/.exec(t);
        let content = m[2];
        if (/^#+$/.test(content)) content = '';
        else content = content.replace(/[ \t]+#+$/, '');
        blocks.push({ type: 'heading', level: m[1].length, text: content });
        i++;
        continue;
      }
      if (kind === 'hr') { blocks.push({ type: 'hr' }); i++; continue; }
      if (kind === 'fence') {
        const fi = fenceInfo(t);
        const fenceCh = fi.ch;
        const fenceLen = fi.len;
        // marked's Dt: dedent each content line by up to the opening
        // fence line's leading-whitespace LENGTH (characters, not columns)
        const fenceWsLen = /^[ \t]*/.exec(t)[0].length;
        let info = fi.info.split(/[ \t]+/)[0];
        info = info.replace(/\\([!"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~])/g, '$1');
        const contentLines = [];
        i++;
        while (i < n) {
          const cl = lines[i].text;
          const cm = /^ {0,3}(`{3,}|~{3,})[ \t]*$/.exec(cl);
          if (cm && cm[1][0] === fenceCh && cm[1].length >= fenceLen) { i++; break; }
          // marked's Dt dedent regex only matches backtick fences: a
          // tilde fence's content is never dedented (doc-22, t3/t5)
          contentLines.push(fenceCh === '`' ? fenceDedent(cl, fenceWsLen) : cl);
          i++;
        }
        // exactly one trailing blank line is dropped (it is the newline
        // that terminates the block, not content)
        if (contentLines.length && contentLines[contentLines.length - 1] === '') contentLines.pop();
        blocks.push({ type: 'code', text: contentLines.join('\n') + (contentLines.length ? '\n' : ''), info, fenced: true });
        continue;
      }
      if (kind === 'html') {
        const hb = htmlBlockStart(t);
        const htmlLines = [t];
        i++;
        const srcEndsWithNL = lines._srcEndsWithNL;
        if (hb.type <= 5) {
          // end when a line contains the end pattern
          if (!hb.endRe.test(t)) {
            while (i < n) {
              const hl = lines[i].text;
              htmlLines.push(hl);
              i++;
              if (hb.endRe.test(hl)) break;
            }
          }
        } else {
          // types 6-7 end at blank line
          while (i < n && !lines[i].blank) { htmlLines.push(lines[i].text); i++; }
        }
        let htmlText = htmlLines.join('\n');
        // trailing \n: types 1-5 include it when the next line is non-blank
        // (or at EOF with source ending \n); types 6-7 only at EOF.
        if (hb.type <= 5) {
          if (i < n && !isBlankLine(lines[i].text)) htmlText += '\n';
          else if (i >= n && srcEndsWithNL) htmlText += '\n';
        } else {
          if (i >= n && srcEndsWithNL) htmlText += '\n';
        }
        blocks.push({ type: 'html', text: htmlText });
        continue;
      }
      if (kind === 'blockquote') {
        const res = collectBlockquote(lines, i, refs);
        blocks.push(res.node);
        i = res.endIdx;
        continue;
      }
      if (kind === 'list') {
        const res = collectList(lines, i, refs);
        blocks.push(res.node);
        i = res.endIdx;
        continue;
      }
    }
    // indented code (cannot interrupt a paragraph)
    if (!inPara && indentOf(t, line.col) >= 4) {
      flushPara();
      const codeLines = [];
      while (i < n) {
        const cl = lines[i];
        if (cl.blank) {
          // blank line: include if followed by more indented code
          let j = i + 1;
          while (j < n && lines[j].blank) j++;
          if (j < n && indentOf(lines[j].text, lines[j].col) >= 4) {
            while (i < j) { codeLines.push(indentedCodeDedent(lines[i].text)); i++; }
            continue;
          }
          break;
        }
        if (indentOf(cl.text, cl.col) < 4) break;
        codeLines.push(indentedCodeDedent(cl.text));
        i++;
      }
      // strip trailing blank lines
      while (codeLines.length && codeLines[codeLines.length - 1] === '') codeLines.pop();
      blocks.push({ type: 'code', text: codeLines.join('\n') + (codeLines.length ? '\n' : ''), info: '', fenced: false });
      continue;
    }
    // paragraph line
    if (!para) para = { lines: [] };
    para.lines.push({ text: t, lazy: line.lazy, blank: false });
    i++;
  }
  flushPara();
  return { blocks, loose };
}

// Extract leading link ref defs from paragraph lines. Registers them in refs
// (first definition wins). Returns the remaining lines.
function extractLinkDefs(paraLines, refs) {
  let idx = 0;
  while (idx < paraLines.length) {
    const d = parseLinkDef(paraLines, idx);
    if (!d) break;
    if (!refs.has(d.label)) refs.set(d.label, { dest: d.dest, title: d.title });
    idx = d.endIdx;
  }
  return paraLines.slice(idx);
}

// Finalize a paragraph: extract link ref defs; if lines remain, make a para node.
function finalizeParagraph(paraLines, refs) {
  const remaining = extractLinkDefs(paraLines, refs);
  if (remaining.length === 0) return null;
  return { type: 'para', text: remaining.map(l => l.text).join('\n') };
}

// ---------------------------------------------------------------- collectors

// Is this line a block start? inPara controls list-interruption rules.
function isBlockStartLine(t, col, inPara) {
  if (/^ {0,3}#{1,6}(?:[ \t]+|$)/.test(t)) return true;
  if (fenceInfo(t)) return true;
  if (/^ {0,3}((?:\* *){3,}|(?:- *){3,}|(?:_ *){3,})[ \t]*$/.test(t)) return true;
  const hb = htmlBlockStart(t);
  if (hb && hb.type <= 6) return true;
  if (stripBlockquoteMarker(t, col)) return true;
  if (indentOf(t, col) >= 4 && !inPara) return true; // indented code can't interrupt a paragraph
  const lm = /^ {0,3}([*+-]|\d{1,9}[.)])(?:[ \t]+|$)/.exec(t);
  if (lm) {
    if (!inPara) return true;
    const after = t.slice(lm[0].length);
    if (/^[ \t]*$/.test(after)) return false;
    if (lm[1] === '*' || lm[1] === '+' || lm[1] === '-') return true;
    return parseInt(lm[1], 10) === 1;
  }
  return false;
}

function collectBlockquote(lines, startIdx, refs) {
  const content = [];
  let i = startIdx;
  let inPara = false;
  let lastWasLazy = false;
  let fenceCh = null, fenceLen = 0; // fenced code state inside the quote
  while (i < lines.length) {
    const line = lines[i];
    const stripped = stripBlockquoteMarker(line.text, line.col);
    if (stripped) {
      content.push({ text: stripped.content, lazy: false, col: stripped.newCol, blank: stripped.content === '' });
      // track fenced code: only marker lines open/close the fence
      if (fenceCh !== null) {
        const cm = new RegExp('^ {0,3}(' + fenceCh + '{' + fenceLen + ',})[ \\t]*$').exec(stripped.content);
        if (cm) { fenceCh = null; fenceLen = 0; }
        inPara = false;
      } else {
        const fi = fenceInfo(stripped.content);
        if (fi) { fenceCh = fi.ch; fenceLen = fi.len; inPara = false; }
        else if (isBlankLine(stripped.content)) inPara = false;
        // a nested blockquote/list may hold an open paragraph, so a lazy
        // line is passed in and the inner parser decides
        else if (/^ {0,3}>/.test(stripped.content) || listMarkerInfo(stripped.content, stripped.newCol)) inPara = true;
        else if (isBlockStartLine(stripped.content, stripped.newCol, inPara)) inPara = false;
        else inPara = true;
      }
      lastWasLazy = false;
      i++;
      continue;
    }
    if (line.blank) break;
    // a lazy line inside a fenced code block ends the blockquote
    if (fenceCh !== null) break;
    if (isBlockStartLine(line.text, line.col, inPara)) break;
    if (!inPara) break; // lazy lines only continue an open paragraph
    // lazy continuation: a would-be indented-code line (indent >= 4) has
    // 4 columns stripped when it continues an open paragraph
    let lazyText = line.text;
    let lazyCol = line.col;
    if (indentOf(lazyText, lazyCol) >= 4) {
      const st = stripIndent(lazyText, 4, lazyCol);
      lazyText = st.rest; lazyCol = st.newCol;
    }
    // quirk: a lazy setext-underline line following a lazy line is indented
    // by 4 spaces (so the re-lexer won't treat it as a setext underline)
    if (lastWasLazy && /^ {0,3}(=+|-+)[ \t]*$/.test(lazyText)) lazyText = '    ' + lazyText;
    content.push({ text: lazyText, lazy: true, col: lazyCol, blank: false });
    inPara = true;
    lastWasLazy = true;
    i++;
  }
  content._inBlockquote = true;
  content._srcEndsWithNL = (i >= lines.length) && !!lines._srcEndsWithNL;
  const inner = parseBlocks(content, refs);
  return { node: { type: 'blockquote', children: inner.blocks }, endIdx: i };
}

// Compute list marker info for a line. Returns null if not a marker.
function listMarkerInfo(t, col) {
  const m = /^ {0,3}([*+-]|\d{1,9}[.)])/.exec(t);
  if (!m) return null;
  const marker = m[1];
  let lead = 0;
  while (lead < t.length && t[lead] === ' ' && lead < 3) lead++;
  const markerEndCol = (col || 0) + lead + marker.length;
  // marked's list rule: expand the tabs in the whitespace after the
  // marker (columns from the marker's end), then the content indent is
  // the expanded whitespace's length in CHARACTERS — but when it exceeds
  // 4 it is treated as 1 (so "-\\t\\tfoo" keeps six spaces of content
  // and becomes indented code, cm-007).
  const afterMarker = t.slice(lead + marker.length);
  const wsRun = /^[ \t]*/.exec(afterMarker)[0];
  const expanded = expandLeadingTabs(wsRun, markerEndCol) + afterMarker.slice(wsRun.length);
  const empty = /^[ \t]*$/.test(afterMarker);
  let contentIndent, content, contentCol;
  if (empty) {
    contentIndent = markerEndCol + 1;
    content = '';
    contentCol = markerEndCol + 1;
  } else {
    let r = expanded.search(/[^ ]/);
    if (r > 4) r = 1;
    contentIndent = markerEndCol + r;
    content = expanded.slice(r);
    contentCol = markerEndCol + r;
  }
  const isOrdered = /^\d/.test(marker);
  return {
    marker, isOrdered,
    bullet: isOrdered ? null : marker,
    delim: isOrdered ? marker[marker.length - 1] : null,
    start: isOrdered ? parseInt(marker, 10) : null,
    contentIndent,
    content,
    contentCol,
    empty,
    lead,
  };
}

function collectList(lines, startIdx, refs) {
  const first = listMarkerInfo(lines[startIdx].text, lines[startIdx].col);
  const items = []; // each: {lines: [{text,lazy,col}], blankBetween: bool}
  let cur = { lines: [], blankBetween: false };
  items.push(cur);
  let listLoose = false;
  let i = startIdx;
  // first line content
  const firstLine = lines[startIdx];
  const firstContent = first.content;
  cur.lines.push({ text: firstContent, lazy: false, col: first.contentCol, blank: isBlankLine(firstContent) });
  let inPara = !isBlankLine(firstContent) &&
    (/^ {0,3}>/.test(firstContent) || listMarkerInfo(firstContent, first.contentCol) ||
      !isBlockStartLine(firstContent, first.contentCol, false));
  // content indent relative to the marker line's start (container content
  // is re-parsed, so indents are relative, not absolute)
  let curContentIndent = first.contentIndent - (firstLine.col || 0);
  i++;
  let pendingBlanks = 0;
  while (i < lines.length) {
    const line = lines[i];
    if (line.blank) { pendingBlanks++; inPara = false; i++; continue; }
    const mi = listMarkerInfo(line.text, line.col);
    const markerIndent = mi ? (line.col || 0) + mi.lead : 0;
    const lineIndent = indentOf(line.text, line.col);
    // a block start that can't be inside the item ends the list
    // (hr / atx / fence / html 1-6 at an indent below the content indent)
    if (lineIndent < curContentIndent) {
      if (/^ {0,3}((?:\*[ \t]*){3,}|(?:-[ \t]*){3,}|(?:_[ \t]*){3,})[ \t]*$/.test(line.text) ||
        /^ {0,3}#{1,6}(?:[ \t]+|$)/.test(line.text) ||
        /^ {0,3}(```+|~~~+)/.test(line.text) ||
        (() => { const hb = htmlBlockStart(line.text); return hb && hb.type <= 6; })()) break;
    }
    // new item of the same list? (marker indent must be < content indent)
    if (mi && mi.isOrdered === first.isOrdered &&
      (first.isOrdered ? mi.delim === first.delim : mi.bullet === first.bullet) &&
      mi.lead <= 3 && mi.lead < curContentIndent) {
      if (pendingBlanks > 0) listLoose = true;
      pendingBlanks = 0;
      cur = { lines: [], blankBetween: false };
      items.push(cur);
      const content = mi.content;
      cur.lines.push({ text: content, lazy: false, col: mi.contentCol, blank: isBlankLine(content) });
      inPara = !isBlankLine(content) &&
        (/^ {0,3}>/.test(content) || listMarkerInfo(content, mi.contentCol) ||
          !isBlockStartLine(content, mi.contentCol, false));
      curContentIndent = mi.contentIndent - (line.col || 0);
      i++;
      continue;
    }
    // different list type -> end of this list
    if (mi && mi.lead <= 3 && mi.lead < curContentIndent) break;
    // inside current item? (indent >= contentIndent)
    if (lineIndent >= curContentIndent) {
      // an empty item cannot gain content after a blank line
      if (pendingBlanks > 0 && cur.lines.every(l => l.blank)) break;
      if (pendingBlanks > 0) { cur.blankBetween = true; for (let b = 0; b < pendingBlanks; b++) cur.lines.push({ text: '', lazy: false, col: line.col, blank: true }); pendingBlanks = 0; }
      // marked's list rule: expand leading tabs to spaces (columns from
      // the line's own start), then drop the content-indent CHARACTERS
      const expandedLine = expandLeadingTabs(line.text, 0);
      const stripped = { rest: expandedLine.slice(curContentIndent), newCol: curContentIndent };
      // a would-be indented-code line (indent >= 4) has 4 columns stripped
      // when it continues an open paragraph inside the item; never strip a
      // nested list marker (it must keep its indent to nest correctly)
      // NOTE: no 4-column strip here: the remaining indent belongs to
      // nested lists, which strip their own indents (stripping 4 here
      // eats columns a deeper list needs; 3-level nesting, doc-01)
      cur.lines.push({ text: stripped.rest, lazy: false, col: stripped.newCol, blank: isBlankLine(stripped.rest) });
      if (isBlankLine(stripped.rest)) inPara = false;
      else if (/^ {0,3}>/.test(stripped.rest) || listMarkerInfo(stripped.rest, stripped.newCol)) inPara = true;
      else if (isBlockStartLine(stripped.rest, stripped.newCol, inPara)) inPara = false;
      else inPara = true;
      i++;
      continue;
    }
    // lazy continuation?
    if (pendingBlanks === 0 && inPara && !isBlockStartLine(line.text, line.col, true)) {
      let lazyText = line.text, lazyCol = line.col;
      if (indentOf(lazyText, lazyCol) >= 4) {
        const st = stripIndent(lazyText, 4, lazyCol);
        lazyText = st.rest; lazyCol = st.newCol;
      }
      cur.lines.push({ text: lazyText, lazy: true, col: lazyCol, blank: false });
      i++;
      continue;
    }
    break;
  }
  // build list node
  const listNode = {
    type: 'list',
    ordered: first.isOrdered,
    start: first.isOrdered ? first.start : null,
    delim: first.delim,
    bullet: first.bullet,
    tight: true,
    items: [],
  };
  let loose = listLoose;
  for (const it of items) {
    // strip trailing blank lines from item
    while (it.lines.length && isBlankLine(it.lines[it.lines.length - 1].text)) it.lines.pop();
    it.lines._inBlockquote = false;
    it.lines._srcEndsWithNL = false;
    const inner = parseBlocks(it.lines, refs, true);
    if (inner.loose) loose = true;
    listNode.items.push({ children: inner.blocks });
  }
  listNode.tight = !loose;
  // back up past blank lines that were consumed as pending but never
  // committed to an item: the outer parser must see them (a blank line
  // between a nested list and following content makes the list loose)
  return { node: listNode, endIdx: i - pendingBlanks, loose };
}

// ---------------------------------------------------------------- renderer

// Task list: [ ], [x] or [X] + spaces + non-whitespace text at the start
// of a list item's first paragraph. Returns {checked, rest} or null.
function taskInfo(text) {
  const m = /^\[( |x|X)\][ \t]+/.exec(text);
  if (!m) return null;
  const rest = text.slice(m[0].length);
  if (!rest || /\s/.test(rest[0])) return null;
  return { checked: m[1] !== ' ', rest };
}

function renderBlocks(blocks, refs, tightList) {
  let out = '';
  for (const b of blocks) {
    switch (b.type) {
      case 'para': {
        let html = parseInline(b.text, refs);
        if (b.task) {
          html = (b.task === 'checked'
            ? '<input checked="" disabled="" type="checkbox">'
            : '<input disabled="" type="checkbox">') + ' ' + html;
        }
        if (tightList) out += html;
        else out += '<p>' + html + '</p>\n';
        break;
      }
      case 'heading':
        out += '<h' + b.level + '>' + parseInline(b.text, refs) + '</h' + b.level + '>\n';
        break;
      case 'code': {
        out += '<pre><code';
        if (b.fenced && b.info) out += ' class="language-' + escNoEncode(b.info) + '"';
        out += '>' + escEncode(b.text) + '</code></pre>\n';
        break;
      }
      case 'html':
        out += b.text;
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'blockquote':
        out += '<blockquote>\n' + renderBlocks(b.children, refs, false) + '</blockquote>\n';
        break;
      case 'list': {
        const tag = b.ordered ? 'ol' : 'ul';
        out += '<' + tag;
        if (b.ordered && b.start !== 1) out += ' start="' + b.start + '"';
        out += '>\n';
        for (const item of b.items) {
          const first = item.children[0];
          if (first && first.type === 'para') {
            const ti = taskInfo(first.text);
            if (ti) { first.text = ti.rest; first.task = ti.checked ? 'checked' : 'unchecked'; }
          }
          out += '<li>';
          out += renderBlocks(item.children, refs, b.tight);
          out += '</li>\n';
        }
        out += '</' + tag + '>\n';
        break;
      }
      case 'table': {
        out += '<table>\n<thead>\n<tr>\n';
        for (let k = 0; k < b.header.length; k++) {
          out += '<th';
          if (b.align[k]) out += ' align="' + b.align[k] + '"';
          out += '>' + parseInline(b.header[k], refs) + '</th>\n';
        }
        out += '</tr>\n</thead>\n';
        if (b.rows.length > 0) {
          out += '<tbody>';
          for (const row of b.rows) {
            out += '<tr>\n';
            for (let k = 0; k < b.header.length; k++) {
              const cell = k < row.length ? row[k] : '';
              out += '<td';
              if (b.align[k]) out += ' align="' + b.align[k] + '"';
              out += '>' + parseInline(cell, refs) + '</td>\n';
            }
            out += '</tr>\n';
          }
          out += '</tbody>';
        }
        out += '</table>\n';
        break;
      }
    }
  }
  return out;
}

// ---------------------------------------------------------------- main entry

export function parse(markdown) {
  const src = markdown.replace(/\r\n?/g, '\n');
  const lines = splitLines(src);
  lines._inBlockquote = false;
  lines._srcEndsWithNL = src.endsWith('\n');
  const refs = new Map();
  const { blocks } = parseBlocks(lines, refs);
  return renderBlocks(blocks, refs, false);
}
