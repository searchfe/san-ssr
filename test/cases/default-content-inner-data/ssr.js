module.exports = function (data, noDataOutput) {
/* eslint no-unused-vars: "off" */
const $version = '3.7.7'

const componentRenderers = {}

function extend (target, source) {
    if (source) {
        Object.keys(source).forEach(function (key) {
            const value = source[key]
            if (typeof value !== 'undefined') {
                target[key] = value
            }
        })
    }

    return target
}

function each (array, iterator) {
    if (array && array.length > 0) {
        for (let i = 0, l = array.length; i < l; i++) {
            if (iterator(array[i], i) === false) {
                break
            }
        }
    }
}

function contains (array, value) {
    let result
    each(array, function (item) {
        result = item === value
        return !result
    })

    return result
}

const HTML_ENTITY = {
    /* jshint ignore:start */
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    '"': '&quot;',
    /* eslint-disable quotes */
    "'": '&#39;'
    /* eslint-enable quotes */
    /* jshint ignore:end */
}

function htmlFilterReplacer (c) {
    return HTML_ENTITY[c]
}

function escapeHTML (source) {
    if (source == null) {
        return ''
    }

    if (typeof source === 'string') {
        return source ? source.replace(/[&<>"']/g, htmlFilterReplacer) : ''
    }

    return '' + source
}

function _classFilter (source) {
    if (source instanceof Array) {
        return source.join(' ')
    }

    return source
}

function _styleFilter (source) {
    if (typeof source === 'object') {
        let result = ''
        if (source) {
            Object.keys(source).forEach(function (key) {
                result += key + ':' + source[key] + ';'
            })
        }

        return result
    }

    return source
}

function _xclassFilter (outer, inner) {
    if (outer instanceof Array) {
        outer = outer.join(' ')
    }

    if (outer) {
        if (inner) {
            return inner + ' ' + outer
        }

        return outer
    }

    return inner
}

function _xstyleFilter (outer, inner) {
    outer = outer && defaultStyleFilter(outer)
    if (outer) {
        if (inner) {
            return inner + ';' + outer
        }

        return outer
    }

    return inner
}

function attrFilter (name, value) {
    if (value) {
        return ' ' + name + '="' + value + '"'
    }

    return ''
}

function boolAttrFilter (name, value) {
    if (value && value !== 'false' && value !== '0') {
        return ' ' + name
    }

    return ''
}

function callFilter (ctx, name, args) {
    const filter = ctx.proto.filters[name]
    if (typeof filter === 'function') {
        return filter.apply(ctx, args)
    }
}

function defaultStyleFilter (source) {
    if (typeof source === 'object') {
        let result = ''
        for (const key in source) {
            /* istanbul ignore else  */
            if (source.hasOwnProperty(key)) {
                result += key + ':' + source[key] + ';'
            }
        }

        return result
    }

    return source
}

componentRenderers._id94 = componentRenderers._id94|| _id94;
var _id94Proto = {
filters: {

},
computed: {

},
computedNames: [

],
tagName: "div"
};
function _id94(data, noDataOutput, parentCtx, tagName, sourceSlots) {
var html = "";
var componentCtx = {
proto: _id94Proto,
sourceSlots: sourceSlots,
data: data || {},
owner: parentCtx,
slotRenderers: {}
};
if (data) {
}
var computedNames = componentCtx.proto.computedNames;
for (var $i = 0; $i < computedNames.length; $i++) {
  var $computedName = computedNames[$i];
  data[$computedName] = componentCtx.proto.computed[$computedName](componentCtx);
}
html += "<div";
if (componentCtx.data.class) {
html += attrFilter("class", escapeHTML(_classFilter(componentCtx.data.class)));
}
if (componentCtx.data.style) {
html += attrFilter("style", escapeHTML(_styleFilter(componentCtx.data.style)));
}
if (componentCtx.data.id) {
html += attrFilter("id", escapeHTML(componentCtx.data.id));
}
html += ">";
if (!noDataOutput) {
html += "<!--s-data:" + JSON.stringify(componentCtx.data) + "-->";
}
componentCtx.slotRenderers._id95 = componentCtx.slotRenderers._id95 || function () {
function $defaultSlotRender(componentCtx) {
  var html = "";
html += "<p>";
html += escapeHTML(componentCtx.data.n) + "," + escapeHTML(componentCtx.data.sex) + "," + escapeHTML(componentCtx.data.email) + " - " + escapeHTML(componentCtx.data.desc);
html += "</p>";

  return html;
}
var $isInserted = false;
var $ctxSourceSlots = componentCtx.sourceSlots;
var $mySourceSlots = [];
if ($ctxSourceSlots[0] && $ctxSourceSlots[0][1] == null) {
  $mySourceSlots.push($ctxSourceSlots[0][0]);
  $isInserted = true;
}
if (!$isInserted) { $mySourceSlots.push($defaultSlotRender); }
var $slotCtx = $isInserted ? componentCtx.owner : componentCtx;
$slotCtx = {data: extend({}, $slotCtx.data), proto: $slotCtx.proto, owner: $slotCtx.owner};
$slotCtx.data["n"] = componentCtx.data.data.name;
$slotCtx.data["email"] = componentCtx.data.data.email;
$slotCtx.data["sex"] = componentCtx.data.data.sex?"male":"female";
for (var $renderIndex = 0; $renderIndex < $mySourceSlots.length; $renderIndex++) {
  html += $mySourceSlots[$renderIndex]($slotCtx);
}
};
componentCtx.slotRenderers._id95();
html += "</div>";
return html;
};
componentRenderers._id93 = componentRenderers._id93|| _id93;
var _id93Proto = {
filters: {

},
computed: {

},
computedNames: [

],
tagName: "div"
};
function _id93(data, noDataOutput, parentCtx, tagName, sourceSlots) {
var html = "";
var componentCtx = {
proto: _id93Proto,
sourceSlots: sourceSlots,
data: data || {},
owner: parentCtx,
slotRenderers: {}
};
if (data) {
}
var computedNames = componentCtx.proto.computedNames;
for (var $i = 0; $i < computedNames.length; $i++) {
  var $computedName = computedNames[$i];
  data[$computedName] = componentCtx.proto.computed[$computedName](componentCtx);
}
html += "<div";
if (componentCtx.data.class) {
html += attrFilter("class", escapeHTML(_classFilter(componentCtx.data.class)));
}
if (componentCtx.data.style) {
html += attrFilter("style", escapeHTML(_styleFilter(componentCtx.data.style)));
}
if (componentCtx.data.id) {
html += attrFilter("id", escapeHTML(componentCtx.data.id));
}
html += ">";
if (!noDataOutput) {
html += "<!--s-data:" + JSON.stringify(componentCtx.data) + "-->";
}
var $sourceSlots = [];
html += componentRenderers._id94(
{"data":componentCtx.data.man,
"desc":componentCtx.data.tip}, true, componentCtx, "x-man", $sourceSlots);
$sourceSlots = null;
html += "</div>";
return html;
};
return componentRenderers._id93(data, noDataOutput)
}