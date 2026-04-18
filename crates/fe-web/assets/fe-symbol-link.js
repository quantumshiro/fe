// <fe-symbol-link> — Inline link to a documented Fe symbol.
//
// Usage:
//   <fe-symbol-link symbol="mylib::Game/struct">Game</fe-symbol-link>
//   <fe-symbol-link symbol="mylib::Game/struct"></fe-symbol-link>
//
// If no text content is provided, the symbol's display name is used.
// Links to the static docs site when FE_DOCS_BASE is set, otherwise
// renders as a hash link with hover info.
//
// Attributes:
//   symbol — doc path (e.g. "mylib::Game/struct")

class FeSymbolLink extends HTMLElement {
  static get observedAttributes() { return ["symbol", "src", "base"]; }

  attributeChangedCallback(name, oldVal, newVal) {
    if (oldVal === newVal) return;
    if (name === "src") { this._loadSrc(); return; }
    this._renderLink();
  }

  connectedCallback() {
    if (this._userText == null) {
      this._userText = this.textContent.trim();
    }
    this._loadSrc();
    this._renderLink();
  }

  _loadSrc() {
    var src = this.getAttribute("src");
    if (!src) return;
    var self = this;
    feLoadSrc(src).then(function (result) {
      self._index = result.index;
      self._scip = result.scip;
      self._renderLink();
    });
  }

  _renderLink() {
    var symbolPath = this.getAttribute("symbol");
    if (!symbolPath) return;

    var index = this._index || window.FE_DOC_INDEX;
    if (!index || !index.items) {
      if (!feWhenReady(this._renderLink.bind(this))) return;
    }

    var item = null;
    if (index && index.items) {
      for (var i = 0; i < index.items.length; i++) {
        if (index.items[i].path === symbolPath) { item = index.items[i]; break; }
      }
    }
    var displayText = this._userText || (item ? item.name : symbolPath.split("::").pop().split("/")[0]);
    var docsBase = this.getAttribute("base") || window.FE_DOCS_BASE;

    var a = document.createElement("a");
    a.className = "fe-symbol-link type-link";
    a.textContent = displayText;
    a.href = (docsBase || "") + "#" + symbolPath;

    feEnrichLink(a, symbolPath);

    // Tooltip fallback from DocIndex
    if (!a.title && item && item.docs && item.docs.summary) {
      a.title = item.docs.summary;
    }

    this.innerHTML = "";
    this.appendChild(a);
  }
}

customElements.define("fe-symbol-link", FeSymbolLink);
