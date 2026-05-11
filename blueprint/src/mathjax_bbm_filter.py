#!/usr/bin/env python3
"""Patch plasTeX HTML output for the blueprint web build."""

from __future__ import annotations

import re
import sys


BBM_CONFIG = """<script>
  MathJax = {
    loader: {
      load: ['[tex]/bbm'],
      paths: {
        mathjax: 'https://cdn.jsdelivr.net/npm/mathjax@4.1.1',
        'mathjax-bbm-extension': 'https://cdn.jsdelivr.net/npm/@mathjax/mathjax-bbm-font-extension@4.1.1'
      }
    },
    output: {
      font: 'mathjax-tex'
    },
    tex: {
      inlineMath: INLINE_MATH,
      packages: {'[+]': ['bbm']}
    }
  };
</script>"""

FONT_PRECONNECT = """<link rel="preconnect" href="https://fonts.googleapis.com" />
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin />"""

EXPANDER_SCRIPT = """<script>
document.addEventListener('DOMContentLoaded', function () {
  var right = String.fromCharCode(0x25b8);
  var down = String.fromCharCode(0x25be);
  var oldDown = String.fromCharCode(0x25bc);

  function normalizeExpander(span) {
    var marker = span.textContent.trim();
    var normalized = (marker === down || marker === oldDown) ? down : right;
    if (span.textContent !== normalized) {
      span.textContent = normalized;
    }
  }

  function normalizeAllExpanders(root) {
    root.querySelectorAll('span.expand-toc, span.expand-proof').forEach(normalizeExpander);
  }

  function eventTargetElement(event) {
    return event.target.nodeType === 1 ? event.target : event.target.parentElement;
  }

  var showmoreUpdate = window.showmore_update;
  function wrapShowmoreUpdate(callback) {
    if (typeof callback !== 'function') {
      return callback;
    }

    return function () {
      var result = callback.apply(this, arguments);
      normalizeAllExpanders(document);
      return result;
    };
  }

  try {
    Object.defineProperty(window, 'showmore_update', {
      configurable: true,
      get: function () {
        return showmoreUpdate;
      },
      set: function (callback) {
        showmoreUpdate = wrapShowmoreUpdate(callback);
      }
    });
    showmoreUpdate = wrapShowmoreUpdate(showmoreUpdate);
  } catch (error) {
    showmoreUpdate = wrapShowmoreUpdate(showmoreUpdate);
  }

  normalizeAllExpanders(document);

  var observer = new MutationObserver(function (mutations) {
    mutations.forEach(function (mutation) {
      var target = mutation.target.nodeType === 1 ? mutation.target : mutation.target.parentElement;
      if (!target) {
        return;
      }

      if (target.matches && target.matches('span.expand-toc, span.expand-proof')) {
        normalizeExpander(target);
      } else if (target.querySelectorAll) {
        normalizeAllExpanders(target);
      }
    });
  });
  observer.observe(document.body, { childList: true, characterData: true, subtree: true });

  var toc = document.querySelector('nav.toc');
  if (toc) {
    toc.addEventListener('click', function (event) {
      var target = eventTargetElement(event);
      var span = target && target.closest && target.closest('span.expand-toc');
      if (!span || !toc.contains(span)) {
        return;
      }

      event.preventDefault();
      event.stopPropagation();
      event.stopImmediatePropagation();

      var expanded = span.textContent.trim() === down;
      if (window.jQuery) {
        window.jQuery(span).siblings('ul').slideToggle('fast');
      } else {
        span.parentElement.querySelectorAll(':scope > ul').forEach(function (list) {
          list.style.display = expanded ? 'none' : 'block';
        });
      }
      span.textContent = expanded ? right : down;
    }, true);
  }

  document.addEventListener('click', function (event) {
    var target = eventTargetElement(event);
    var heading = target && target.closest && target.closest('div.proof_heading');
    if (!heading) {
      return;
    }

    var span = heading.querySelector('span.expand-proof');
    if (!span) {
      return;
    }

    event.preventDefault();
    event.stopPropagation();
    event.stopImmediatePropagation();

    var expanded = span.textContent.trim() === down;
    if (window.jQuery) {
      window.jQuery(heading).siblings('div.proof_content').slideToggle();
    } else {
      heading.parentElement.querySelectorAll(':scope > div.proof_content').forEach(function (proof) {
        proof.style.display = expanded ? 'none' : 'block';
      });
    }
    span.textContent = expanded ? right : down;
  }, true);
});
</script>"""


def add_bbm_to_mathjax_config(html: str) -> str:
    """Patch MathJax config blocks produced by plasTeX and plastexdepgraph."""

    def replacement(match: re.Match[str]) -> str:
        inline_math = match.group("inline")
        return BBM_CONFIG.replace("INLINE_MATH", inline_math)

    legacy_pattern = re.compile(
        r"<script type=\"text/x-mathjax-config\">\s*"
        r"MathJax\.Hub\.Config\(\{tex2jax: \{inlineMath: (?P<inline>[^;]+?)\}\}\);\s*"
        r"</script>",
        re.DOTALL,
    )
    html = legacy_pattern.sub(replacement, html)

    modern_pattern = re.compile(
        r"<script>\s*MathJax = \{\s*tex: \{\s*"
        r"inlineMath: (?P<inline>\[[^\n]+?\])\s*"
        r"\}\s*\}\s*</script>",
        re.DOTALL,
    )
    return modern_pattern.sub(replacement, html)


def add_font_preconnect(html: str) -> str:
    """Add early Google Fonts connection hints before stylesheet discovery."""

    if 'rel="preconnect" href="https://fonts.googleapis.com"' in html:
        return html
    return html.replace('<link rel="stylesheet"', f"{FONT_PRECONNECT}\n<link rel=\"stylesheet\"", 1)


def trim_theorem_captions(html: str) -> str:
    """Remove plasTeX whitespace inside theorem caption spans."""

    caption_pattern = re.compile(
        r'(<span class="[^"]+_thmcaption">)(?P<caption>.*?)(</span>)',
        re.DOTALL,
    )

    def replacement(match: re.Match[str]) -> str:
        return f"{match.group(1)}{match.group('caption').strip()}{match.group(3)}"

    return caption_pattern.sub(replacement, html)


def normalize_expanders(html: str) -> str:
    old_right = chr(0x25B6)
    old_down = chr(0x25BC)
    right = chr(0x25B8)
    down = chr(0x25BE)

    for class_name in ("expand-toc", "expand-proof"):
        html = (
            html.replace(
                f'<span class="{class_name}">{old_right}</span>',
                f'<span class="{class_name}">{right}</span>',
            )
            .replace(
                f'<span class="{class_name}">{old_down}</span>',
                f'<span class="{class_name}">{down}</span>',
            )
        )
    return html


def add_expander_script(html: str) -> str:
    """Keep plasTeX's toggles on the normalized glyph pair."""

    if "normalizeExpander" in html:
        return html
    return html.replace("</head>", f"{EXPANDER_SCRIPT}\n</head>", 1)


html = add_bbm_to_mathjax_config(sys.stdin.read())
html = add_font_preconnect(html)
html = normalize_expanders(html)
html = add_expander_script(html)
sys.stdout.write(trim_theorem_captions(html))
