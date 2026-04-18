// <fe-doc-nav> — Navigable module tree for Fe documentation.
//
// Renders a hierarchical module tree from docs.json data.  Dispatches
// `fe-navigate` events when an item is clicked so the host page controls
// how navigation happens.
//
// Usage:
//   <fe-doc-nav src="/docs.json"></fe-doc-nav>
//   <fe-doc-nav src="/docs.json" filter="core::*,std::*" exclude="core::intrinsic"></fe-doc-nav>
//
// Attributes:
//   src          — URL to docs.json (uses shared fetch cache)
//   filter       — comma-separated glob patterns; only show matching modules/items
//   filter-kind  — comma-separated kinds to include (e.g. "trait,struct")
//   exclude      — comma-separated glob patterns to hide
//   active       — currently active doc path (highlights in tree)
//   show-search  — include the search box at the top

class FeDocNav extends HTMLElement {
  static get observedAttributes() {
    return ["src", "filter", "filter-kind", "exclude", "active", "show-search"];
  }

  attributeChangedCallback(name, oldVal, newVal) {
    if (oldVal === newVal) return;
    if (name === "src") { this._loadSrc(); return; }
    this._render();
  }

  connectedCallback() {
    this._loadSrc();
    this._render();
  }

  _loadSrc() {
    var src = this.getAttribute("src");
    if (!src) return;
    var self = this;
    feLoadSrc(src).then(function (result) {
      self._index = result.index;
      self._render();
    });
  }

  _getIndex() {
    return this._index || window.FE_DOC_INDEX || { items: [], modules: [] };
  }

  _matchesFilter(path) {
    var filter = this.getAttribute("filter");
    if (!filter) return true;
    var patterns = filter.split(",");
    for (var i = 0; i < patterns.length; i++) {
      var pat = patterns[i].trim();
      if (!pat) continue;
      if (pat.endsWith("*")) {
        if (path.indexOf(pat.slice(0, -1)) === 0) return true;
      } else {
        if (path === pat || path.indexOf(pat + "::") === 0) return true;
      }
    }
    return false;
  }

  _isExcluded(path) {
    var exclude = this.getAttribute("exclude");
    if (!exclude) return false;
    var patterns = exclude.split(",");
    for (var i = 0; i < patterns.length; i++) {
      var pat = patterns[i].trim();
      if (!pat) continue;
      if (pat.endsWith("*")) {
        if (path.indexOf(pat.slice(0, -1)) === 0) return true;
      } else {
        if (path === pat || path.indexOf(pat + "::") === 0) return true;
      }
    }
    return false;
  }

  _matchesKind(kind) {
    var filterKind = this.getAttribute("filter-kind");
    if (!filterKind) return true;
    var kinds = filterKind.split(",");
    for (var i = 0; i < kinds.length; i++) {
      if (kinds[i].trim() === kind) return true;
    }
    return false;
  }

  _render() {
    var index = this._getIndex();
    if (!index.modules || index.modules.length === 0) {
      // Not loaded yet — wait for fe-web-ready
      if (!this._waiting) {
        this._waiting = true;
        var self = this;
        document.addEventListener("fe-web-ready", function onReady() {
          document.removeEventListener("fe-web-ready", onReady);
          self._waiting = false;
          self._render();
        });
      }
      return;
    }

    var active = this.getAttribute("active") || "";
    var self = this;

    var html = '<nav class="fe-doc-nav">';

    if (this.hasAttribute("show-search")) {
      html += '<div class="fe-doc-nav-search"><fe-search></fe-search></div>';
    }

    html += '<div class="fe-doc-nav-tree">';
    var modules = index.modules || [];
    for (var i = 0; i < modules.length; i++) {
      html += this._renderModule(modules[i], active);
    }
    if (index.builtin_modules) {
      for (var j = 0; j < index.builtin_modules.length; j++) {
        html += this._renderModule(index.builtin_modules[j], active);
      }
    }
    html += '</div></nav>';

    this.innerHTML = html;

    // Attach click handlers that dispatch fe-navigate
    var links = this.querySelectorAll("a[data-doc-path]");
    for (var k = 0; k < links.length; k++) {
      links[k].addEventListener("click", function (e) {
        e.preventDefault();
        var docPath = this.getAttribute("data-doc-path");
        var ev = new CustomEvent("fe-navigate", {
          bubbles: true, composed: true, cancelable: true,
          detail: { docPath: docPath }
        });
        self.dispatchEvent(ev);
      });
    }
  }

  _renderModule(mod, active) {
    if (this._isExcluded(mod.path)) return "";
    if (!this._matchesFilter(mod.path)) return "";

    var modUrl = mod.path + "/mod";
    var isCurrent = modUrl === active;
    var isExpanded = isCurrent
      || active.indexOf(mod.path + "::") === 0
      || active.indexOf(mod.path + "/") === 0;

    var html = '<details class="fe-nav-module"' + (isExpanded ? " open" : "") + ">";
    html += '<summary class="' + (isCurrent ? "fe-nav-mod-name current" : "fe-nav-mod-name") + '">';
    html += '<a href="#' + _feEsc(modUrl) + '" data-doc-path="' + _feEsc(modUrl) + '">' + _feEsc(mod.name) + "</a>";
    html += "</summary>";
    html += '<div class="fe-nav-mod-content">';

    // Sub-modules
    if (mod.children) {
      for (var i = 0; i < mod.children.length; i++) {
        html += this._renderModule(mod.children[i], active);
      }
    }

    // Items, grouped by kind
    if (mod.items && mod.items.length > 0) {
      var items = this._filterItems(mod.items);
      if (items.length > 0) {
        var grouped = _feGroupByKind(items);
        for (var g = 0; g < grouped.length; g++) {
          var group = grouped[g];
          html += '<div class="fe-nav-kind-group">';
          html += '<h4 class="fe-nav-kind-header">' + _feEsc(group.plural) + "</h4>";
          html += '<ul class="fe-nav-items">';
          for (var j = 0; j < group.items.length; j++) {
            var item = group.items[j];
            var itemUrl = item.path + "/" + _feKindStr(item.kind);
            var itemCurrent = itemUrl === active;
            html += '<li class="' + (itemCurrent ? "current" : "") + '">';
            html += '<a href="#' + _feEsc(itemUrl) + '" data-doc-path="' + _feEsc(itemUrl) + '">';
            html += '<span class="fe-nav-badge ' + _feEsc(_feKindStr(item.kind)) + '">' +
              _feEsc(_feKindStr(item.kind)) + "</span> ";
            html += _feEsc(item.name);
            html += "</a></li>";
          }
          html += "</ul></div>";
        }
      }
    }

    html += "</div></details>";
    return html;
  }

  _filterItems(items) {
    var result = [];
    for (var i = 0; i < items.length; i++) {
      var item = items[i];
      if (this._isExcluded(item.path)) continue;
      if (!this._matchesFilter(item.path)) continue;
      if (!this._matchesKind(item.kind)) continue;
      result.push(item);
    }
    return result;
  }
}

// Shared helpers (keep small, avoid duplicating fe-web.js internals)
var _FE_KIND_INFO = {
  module: { str: "mod", plural: "Modules", order: 0 },
  function: { str: "fn", plural: "Functions", order: 6 },
  struct: { str: "struct", plural: "Structs", order: 3 },
  enum: { str: "enum", plural: "Enums", order: 4 },
  trait: { str: "trait", plural: "Traits", order: 1 },
  contract: { str: "contract", plural: "Contracts", order: 2 },
  type_alias: { str: "type", plural: "Type Aliases", order: 5 },
  "const": { str: "const", plural: "Constants", order: 7 },
};

function _feKindStr(kind) {
  return (_FE_KIND_INFO[kind] || {}).str || kind;
}

function _feEsc(s) {
  var d = document.createElement("div");
  d.textContent = s;
  return d.innerHTML;
}

function _feGroupByKind(items) {
  var groups = {};
  var order = {};
  for (var i = 0; i < items.length; i++) {
    var item = items[i];
    var info = _FE_KIND_INFO[item.kind] || { str: item.kind, plural: item.kind, order: 99 };
    if (!groups[item.kind]) {
      groups[item.kind] = { kind: info.str, plural: info.plural, items: [] };
      order[item.kind] = info.order;
    }
    groups[item.kind].items.push(item);
  }
  var keys = Object.keys(groups);
  keys.sort(function (a, b) { return order[a] - order[b]; });
  var result = [];
  for (var k = 0; k < keys.length; k++) {
    result.push(groups[keys[k]]);
  }
  return result;
}

customElements.define("fe-doc-nav", FeDocNav);
