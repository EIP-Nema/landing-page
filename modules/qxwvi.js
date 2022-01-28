function noop() { }
const identity = x => x;
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentElement !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    node.parentNode.removeChild(node);
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.wholeText !== data)
        text.data = data;
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, bubbles = false) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, false, detail);
    return e;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { stylesheet } = info;
            let i = stylesheet.cssRules.length;
            while (i--)
                stylesheet.deleteRule(i);
            info.rules = {};
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}

const dirty_components = [];
const binding_callbacks = [];
const render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        while (flushidx < dirty_components.length) {
            const component = dirty_components[flushidx];
            flushidx++;
            set_current_component(component);
            update(component.$$);
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    let config = fn(node, params);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config();
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, on_mount, on_destroy, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = on_mount.map(run).filter(is_function);
            if (on_destroy) {
                on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: null,
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

/* generated by Svelte v3.44.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	child_ctx[9] = i;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].link;
	child_ctx[9] = i;
	return child_ctx;
}

// (7:8) {:else}
function create_else_block(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (5:8) {#if logo.image.url}
function create_if_block_1(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { class: true, src: true, alt: true });
			this.h();
		},
		h() {
			attr(img, "class", "img-size svelte-1yij1fo");
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (29:6) {#each cta as {link}
function create_each_block_2(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
			attr(a, "class", "svelte-1yij1fo");
			toggle_class(a, "button", /*cta*/ ctx[2].length - 1 === /*i*/ ctx[9]);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*cta*/ 4 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*cta*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*cta*/ 4) {
				toggle_class(a, "button", /*cta*/ ctx[2].length - 1 === /*i*/ ctx[9]);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (33:4) {#if mobileNavOpen}
function create_if_block(ctx) {
	let nav_1;
	let a;
	let t0;
	let t1;
	let t2;
	let hr;
	let t3;
	let t4;
	let button;
	let svg;
	let path;
	let nav_1_transition;
	let current;
	let mounted;
	let dispose;
	let each_value_1 = /*nav*/ ctx[1];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	let each_value = /*cta*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			nav_1 = element("nav");
			a = element("a");
			t0 = text("Logo");
			t1 = space();

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t2 = space();
			hr = element("hr");
			t3 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			button = element("button");
			svg = svg_element("svg");
			path = svg_element("path");
			this.h();
		},
		l(nodes) {
			nav_1 = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_1_nodes = children(nav_1);
			a = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, "Logo");
			a_nodes.forEach(detach);
			t1 = claim_space(nav_1_nodes);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(nav_1_nodes);
			}

			t2 = claim_space(nav_1_nodes);
			hr = claim_element(nav_1_nodes, "HR", { class: true });
			t3 = claim_space(nav_1_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			t4 = claim_space(nav_1_nodes);

			button = claim_element(nav_1_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);

			svg = claim_svg_element(button_nodes, "svg", {
				xmlns: true,
				viewBox: true,
				fill: true,
				class: true
			});

			var svg_nodes = children(svg);

			path = claim_svg_element(svg_nodes, "path", {
				fill: true,
				"fill-rule": true,
				d: true,
				"clip-rule": true
			});

			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			button_nodes.forEach(detach);
			nav_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", "/");
			attr(a, "class", "logo svelte-1yij1fo");
			attr(hr, "class", "svelte-1yij1fo");
			attr(path, "fill", "currentColor");
			attr(path, "fill-rule", "evenodd");
			attr(path, "d", "M4.293 4.293a1 1 0 011.414 0L10 8.586l4.293-4.293a1 1 0 111.414 1.414L11.414 10l4.293 4.293a1 1 0 01-1.414 1.414L10 11.414l-4.293 4.293a1 1 0 01-1.414-1.414L8.586 10 4.293 5.707a1 1 0 010-1.414z");
			attr(path, "clip-rule", "evenodd");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg, "viewBox", "0 0 20 20");
			attr(svg, "fill", "currentColor");
			attr(svg, "class", "svelte-1yij1fo");
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-1yij1fo");
			attr(nav_1, "id", "mobile-nav");
			attr(nav_1, "class", "svelte-1yij1fo");
		},
		m(target, anchor) {
			insert_hydration(target, nav_1, anchor);
			append_hydration(nav_1, a);
			append_hydration(a, t0);
			append_hydration(nav_1, t1);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].m(nav_1, null);
			}

			append_hydration(nav_1, t2);
			append_hydration(nav_1, hr);
			append_hydration(nav_1, t3);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(nav_1, null);
			}

			append_hydration(nav_1, t4);
			append_hydration(nav_1, button);
			append_hydration(button, svg);
			append_hydration(svg, path);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[5]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 2) {
				each_value_1 = /*nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(nav_1, t2);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*cta*/ 4) {
				each_value = /*cta*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, t4);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;

			add_render_callback(() => {
				if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, true);
				nav_1_transition.run(1);
			});

			current = true;
		},
		o(local) {
			if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, false);
			nav_1_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav_1);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			if (detaching && nav_1_transition) nav_1_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (36:6) {#each nav as {link}}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
			attr(a, "class", "link svelte-1yij1fo");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 2 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (40:6) {#each cta as {link}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[7].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[7].url);
			attr(a, "class", "svelte-1yij1fo");
			toggle_class(a, "button", /*cta*/ ctx[2].length - 1 === /*i*/ ctx[9]);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*cta*/ 4 && t_value !== (t_value = /*link*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*cta*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*cta*/ 4) {
				toggle_class(a, "button", /*cta*/ ctx[2].length - 1 === /*i*/ ctx[9]);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment(ctx) {
	let header;
	let div1;
	let nav_1;
	let a0;
	let t0;
	let a1;
	let t1;
	let t2;
	let a2;
	let t3;
	let t4;
	let a3;
	let t5;
	let t6;
	let a4;
	let t7;
	let t8;
	let div0;
	let button;
	let svg;
	let path;
	let t9;
	let t10;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].image.url) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type(ctx);
	let each_value_2 = /*cta*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	let if_block1 = /*mobileNavOpen*/ ctx[3] && create_if_block(ctx);

	return {
		c() {
			header = element("header");
			div1 = element("div");
			nav_1 = element("nav");
			a0 = element("a");
			if_block0.c();
			t0 = space();
			a1 = element("a");
			t1 = text("Features");
			t2 = space();
			a2 = element("a");
			t3 = text("FAQ");
			t4 = space();
			a3 = element("a");
			t5 = text("Community");
			t6 = space();
			a4 = element("a");
			t7 = text("Team");
			t8 = space();
			div0 = element("div");
			button = element("button");
			svg = svg_element("svg");
			path = svg_element("path");
			t9 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t10 = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			header = claim_element(nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			nav_1 = claim_element(div1_nodes, "NAV", { class: true });
			var nav_1_nodes = children(nav_1);
			a0 = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(nav_1_nodes);
			a1 = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t1 = claim_text(a1_nodes, "Features");
			a1_nodes.forEach(detach);
			t2 = claim_space(nav_1_nodes);
			a2 = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			t3 = claim_text(a2_nodes, "FAQ");
			a2_nodes.forEach(detach);
			t4 = claim_space(nav_1_nodes);
			a3 = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a3_nodes = children(a3);
			t5 = claim_text(a3_nodes, "Community");
			a3_nodes.forEach(detach);
			t6 = claim_space(nav_1_nodes);
			a4 = claim_element(nav_1_nodes, "A", { href: true, class: true });
			var a4_nodes = children(a4);
			t7 = claim_text(a4_nodes, "Team");
			a4_nodes.forEach(detach);
			nav_1_nodes.forEach(detach);
			t8 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			button = claim_element(div0_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);

			svg = claim_svg_element(button_nodes, "svg", {
				width: true,
				height: true,
				viewBox: true,
				fill: true,
				xmlns: true
			});

			var svg_nodes = children(svg);
			path = claim_svg_element(svg_nodes, "path", { d: true, fill: true });
			children(path).forEach(detach);
			svg_nodes.forEach(detach);
			button_nodes.forEach(detach);
			t9 = claim_space(div0_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			t10 = claim_space(div1_nodes);
			if (if_block1) if_block1.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "nemastudio.app");
			attr(a0, "class", "logo svelte-1yij1fo");
			attr(a1, "href", "#features");
			attr(a1, "class", "link svelte-1yij1fo");
			attr(a2, "href", "#faq");
			attr(a2, "class", "link svelte-1yij1fo");
			attr(a3, "href", "#community");
			attr(a3, "class", "link svelte-1yij1fo");
			attr(a4, "href", "#team");
			attr(a4, "class", "link svelte-1yij1fo");
			attr(nav_1, "class", "svelte-1yij1fo");
			attr(path, "d", "M19.4643 17.0213H0.535714C0.239866 17.0213 0 17.3071 0 17.6596V19.3617C0 19.7142 0.239866 20 0.535714 20H19.4643C19.7601 20 20 19.7142 20 19.3617V17.6596C20 17.3071 19.7601 17.0213 19.4643 17.0213ZM19.4643 8.51064H0.535714C0.239866 8.51064 0 8.79644 0 9.14894V10.8511C0 11.2036 0.239866 11.4894 0.535714 11.4894H19.4643C19.7601 11.4894 20 11.2036 20 10.8511V9.14894C20 8.79644 19.7601 8.51064 19.4643 8.51064ZM19.4643 0H0.535714C0.239866 0 0 0.285797 0 0.638296V2.34042C0 2.69292 0.239866 2.97872 0.535714 2.97872H19.4643C19.7601 2.97872 20 2.69292 20 2.34042V0.638296C20 0.285797 19.7601 0 19.4643 0Z");
			attr(path, "fill", "currentColor");
			attr(svg, "width", "20");
			attr(svg, "height", "20");
			attr(svg, "viewBox", "0 0 20 20");
			attr(svg, "fill", "none");
			attr(svg, "xmlns", "http://www.w3.org/2000/svg");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(button, "class", "svelte-1yij1fo");
			attr(div0, "class", "call-to-action svelte-1yij1fo");
			attr(div1, "class", "page-container svelte-1yij1fo");
			attr(header, "class", "svelte-1yij1fo");
		},
		m(target, anchor) {
			insert_hydration(target, header, anchor);
			append_hydration(header, div1);
			append_hydration(div1, nav_1);
			append_hydration(nav_1, a0);
			if_block0.m(a0, null);
			append_hydration(nav_1, t0);
			append_hydration(nav_1, a1);
			append_hydration(a1, t1);
			append_hydration(nav_1, t2);
			append_hydration(nav_1, a2);
			append_hydration(a2, t3);
			append_hydration(nav_1, t4);
			append_hydration(nav_1, a3);
			append_hydration(a3, t5);
			append_hydration(nav_1, t6);
			append_hydration(nav_1, a4);
			append_hydration(a4, t7);
			append_hydration(div1, t8);
			append_hydration(div1, div0);
			append_hydration(div0, button);
			append_hydration(button, svg);
			append_hydration(svg, path);
			append_hydration(div0, t9);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(div0, null);
			}

			append_hydration(div1, t10);
			if (if_block1) if_block1.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[4]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if_block0.d(1);
				if_block0 = current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*cta*/ 4) {
				each_value_2 = /*cta*/ ctx[2];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div0, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_2.length;
			}

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block1, 1);
					}
				} else {
					if_block1 = create_if_block(ctx);
					if_block1.c();
					transition_in(if_block1, 1);
					if_block1.m(div1, null);
				}
			} else if (if_block1) {
				group_outros();

				transition_out(if_block1, 1, 1, () => {
					if_block1 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block1);
			current = true;
		},
		o(local) {
			transition_out(if_block1);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(header);
			if_block0.d();
			destroy_each(each_blocks, detaching);
			if (if_block1) if_block1.d();
			mounted = false;
			dispose();
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { logo = {
		"title": "Nema",
		"image": {
			"alt": "",
			"url": "data:image/svg+xml,%3csvg width='1964' height='800' viewBox='0 0 1964 800' fill='none' xmlns='http://www.w3.org/2000/svg'%3e %3cpath d='M300 660C277.909 660 260 642.091 260 620C260 597.909 277.909 580 300 580L300 660ZM428.284 371.716L511.716 455.147L455.147 511.716L371.716 428.284L428.284 371.716ZM426.863 660L300 660L300 580L426.863 580L426.863 660ZM511.716 455.147C587.312 530.743 533.771 660 426.863 660L426.863 580C462.499 580 480.346 536.914 455.147 511.716L511.716 455.147Z' fill='%23FF0149'/%3e %3cpath d='M500 140C522.091 140 540 157.909 540 180C540 202.091 522.091 220 500 220L500 140ZM371.716 428.284L288.284 344.853L344.853 288.284L428.284 371.716L371.716 428.284ZM373.137 140L500 140L500 220L373.137 220L373.137 140ZM288.284 344.853C212.688 269.257 266.229 140 373.137 140L373.137 220C337.501 220 319.654 263.086 344.853 288.284L288.284 344.853Z' fill='%23FF0149'/%3e %3cpath d='M660 300C660 277.909 642.091 260 620 260C597.909 260 580 277.909 580 300L660 300ZM371.716 428.284L455.147 511.716L511.716 455.147L428.284 371.716L371.716 428.284ZM660 426.863L660 300L580 300L580 426.863L660 426.863ZM455.147 511.716C530.743 587.312 660 533.771 660 426.863L580 426.863C580 462.499 536.914 480.346 511.716 455.147L455.147 511.716Z' fill='black'/%3e %3cpath d='M140 500C140 522.091 157.909 540 180 540C202.091 540 220 522.091 220 500L140 500ZM428.284 371.716L344.853 288.284L288.284 344.853L371.716 428.284L428.284 371.716ZM140 373.137L140 500L220 500L220 373.137L140 373.137ZM344.853 288.284C269.257 212.688 140 266.229 140 373.137L220 373.137C220 337.501 263.086 319.654 288.284 344.853L344.853 288.284Z' fill='black'/%3e %3cg clip-path='url(%23clip0_72_232)'%3e %3cellipse cx='620' cy='180' rx='40' ry='40' transform='rotate(-180 620 180)' fill='%23FF0149'/%3e %3c/g%3e %3cg clip-path='url(%23clip1_72_232)'%3e %3cellipse cx='180' cy='620' rx='40' ry='40' fill='%23FF0149'/%3e %3c/g%3e %3cpath d='M1004.57 260C1020.65 260 1033.69 273.037 1033.69 289.12V482.8C1033.69 500.473 1019.36 514.8 1001.69 514.8H1000.41C990.827 514.8 981.753 510.51 975.675 503.108L858.24 360.1V485.68C858.24 501.763 845.203 514.8 829.12 514.8C813.037 514.8 800 501.763 800 485.68V292C800 274.327 814.327 260 832 260H833.619C843.213 260 852.3 264.304 858.378 271.727L975.448 414.7V289.12C975.448 273.037 988.485 260 1004.57 260Z' fill='black'/%3e %3cpath d='M1234.16 467.48C1247.22 467.48 1257.82 478.073 1257.82 491.14C1257.82 504.207 1247.22 514.8 1234.16 514.8H1097.69C1080.01 514.8 1065.69 500.473 1065.69 482.8V292C1065.69 274.327 1080.01 260 1097.69 260H1229.42C1242.49 260 1253.08 270.593 1253.08 283.66C1253.08 296.727 1242.49 307.32 1229.42 307.32H1124.29V362.648H1214.5C1227.17 362.648 1237.43 372.915 1237.43 385.58C1237.43 398.245 1227.17 408.512 1214.5 408.512H1124.29V467.48H1234.16Z' fill='black'/%3e %3cpath d='M1345.14 380.4L1392.9 476.576C1397.16 483.586 1404.78 487.864 1412.98 487.864C1421.19 487.864 1428.8 483.586 1433.06 476.576L1480.82 380.4V487.136C1480.82 502.414 1493.2 514.8 1508.48 514.8C1523.76 514.8 1536.15 502.414 1536.15 487.136V291.165C1536.15 273.953 1522.19 260 1504.98 260C1494.05 260 1483.92 265.724 1478.28 275.086L1412.98 406.4L1347.68 275.086C1342.04 265.724 1331.91 260 1320.98 260C1303.77 260 1289.82 273.953 1289.82 291.165V487.136C1289.82 502.414 1302.2 514.8 1317.48 514.8C1332.76 514.8 1345.14 502.414 1345.14 487.136V380.4Z' fill='black'/%3e %3cpath d='M1754.68 460.2H1636.38L1620.8 497.897C1616.57 508.127 1606.6 514.8 1595.53 514.8C1575.72 514.8 1562.48 494.405 1570.55 476.315L1655.1 286.615C1662.31 270.427 1678.38 260 1696.1 260C1713.8 260 1729.85 270.405 1737.08 286.566L1821.51 475.393C1829.79 493.905 1816.24 514.8 1795.97 514.8C1784.64 514.8 1774.43 507.973 1770.1 497.506L1754.68 460.2ZM1736.12 415.428L1695.72 317.876L1655.31 415.428H1736.12Z' fill='black'/%3e %3cpath d='M831.602 556.8C831.466 555.096 830.827 553.766 829.685 552.811C828.56 551.857 826.847 551.38 824.545 551.38C823.08 551.38 821.878 551.559 820.94 551.917C820.02 552.257 819.338 552.726 818.895 553.323C818.452 553.919 818.222 554.601 818.205 555.368C818.17 555.999 818.281 556.57 818.537 557.081C818.81 557.576 819.236 558.027 819.815 558.436C820.395 558.828 821.136 559.186 822.04 559.51C822.943 559.834 824.017 560.124 825.261 560.38L829.557 561.3C832.455 561.914 834.935 562.723 836.997 563.729C839.06 564.735 840.747 565.919 842.06 567.283C843.372 568.63 844.335 570.147 844.949 571.834C845.58 573.522 845.903 575.363 845.92 577.357C845.903 580.8 845.043 583.715 843.338 586.101C841.634 588.488 839.196 590.303 836.026 591.547C832.872 592.792 829.08 593.414 824.648 593.414C820.097 593.414 816.125 592.74 812.733 591.394C809.358 590.047 806.733 587.976 804.858 585.181C803 582.368 802.063 578.772 802.045 574.391H815.545C815.631 575.993 816.031 577.34 816.747 578.431C817.463 579.522 818.469 580.348 819.764 580.911C821.077 581.473 822.636 581.755 824.443 581.755C825.96 581.755 827.23 581.567 828.253 581.192C829.276 580.817 830.051 580.297 830.58 579.632C831.108 578.968 831.381 578.209 831.398 577.357C831.381 576.556 831.116 575.857 830.605 575.26C830.111 574.647 829.293 574.101 828.151 573.624C827.009 573.13 825.466 572.669 823.523 572.243L818.307 571.118C813.67 570.113 810.014 568.434 807.338 566.081C804.679 563.712 803.358 560.482 803.375 556.391C803.358 553.067 804.244 550.161 806.034 547.672C807.841 545.167 810.338 543.215 813.526 541.817C816.73 540.419 820.403 539.721 824.545 539.721C828.773 539.721 832.429 540.428 835.514 541.843C838.599 543.257 840.977 545.252 842.648 547.826C844.335 550.382 845.188 553.374 845.205 556.8H831.602Z' fill='black'/%3e %3cpath d='M998.339 551.891V540.436H1043.85V551.891H1028.1V592.8H1014.09V551.891H998.339Z' fill='black'/%3e %3cpath d='M1229.16 540.436H1243.37V573.982C1243.37 577.971 1242.42 581.422 1240.51 584.337C1238.62 587.235 1235.97 589.476 1232.58 591.061C1229.19 592.63 1225.25 593.414 1220.77 593.414C1216.25 593.414 1212.3 592.63 1208.91 591.061C1205.51 589.476 1202.87 587.235 1200.98 584.337C1199.1 581.422 1198.17 577.971 1198.17 573.982V540.436H1212.38V572.755C1212.38 574.374 1212.74 575.823 1213.46 577.101C1214.17 578.363 1215.16 579.351 1216.42 580.067C1217.7 580.783 1219.15 581.141 1220.77 581.141C1222.41 581.141 1223.85 580.783 1225.12 580.067C1226.38 579.351 1227.37 578.363 1228.08 577.101C1228.8 575.823 1229.16 574.374 1229.16 572.755V540.436Z' fill='black'/%3e %3cpath d='M1418.71 592.8H1398.56V540.436H1418.51C1423.89 540.436 1428.55 541.485 1432.47 543.581C1436.4 545.661 1439.44 548.661 1441.57 552.581C1443.72 556.485 1444.79 561.164 1444.79 566.618C1444.79 572.073 1443.73 576.76 1441.59 580.681C1439.46 584.584 1436.45 587.584 1432.54 589.681C1428.64 591.76 1424.03 592.8 1418.71 592.8ZM1412.78 580.732H1418.2C1420.79 580.732 1423 580.314 1424.82 579.479C1426.66 578.644 1428.06 577.203 1429.02 575.158C1429.99 573.113 1430.47 570.266 1430.47 566.618C1430.47 562.971 1429.98 560.124 1428.99 558.078C1428.02 556.033 1426.59 554.593 1424.69 553.757C1422.82 552.922 1420.52 552.505 1417.79 552.505H1412.78V580.732Z' fill='black'/%3e %3cpath d='M1614.18 540.436V592.8H1599.96V540.436H1614.18Z' fill='black'/%3e %3cpath d='M1820.08 566.618C1820.08 572.448 1818.95 577.365 1816.68 581.371C1814.42 585.36 1811.36 588.385 1807.5 590.448C1803.65 592.493 1799.36 593.516 1794.62 593.516C1789.84 593.516 1785.53 592.485 1781.68 590.422C1777.84 588.343 1774.79 585.309 1772.53 581.32C1770.28 577.314 1769.15 572.414 1769.15 566.618C1769.15 560.789 1770.28 555.88 1772.53 551.891C1774.79 547.885 1777.84 544.86 1781.68 542.814C1785.53 540.752 1789.84 539.721 1794.62 539.721C1799.36 539.721 1803.65 540.752 1807.5 542.814C1811.36 544.86 1814.42 547.885 1816.68 551.891C1818.95 555.88 1820.08 560.789 1820.08 566.618ZM1805.46 566.618C1805.46 563.482 1805.04 560.84 1804.21 558.692C1803.39 556.527 1802.17 554.891 1800.55 553.783C1798.95 552.658 1796.97 552.096 1794.62 552.096C1792.27 552.096 1790.28 552.658 1788.66 553.783C1787.06 554.891 1785.84 556.527 1785 558.692C1784.19 560.84 1783.78 563.482 1783.78 566.618C1783.78 569.755 1784.19 572.405 1785 574.57C1785.84 576.718 1787.06 578.354 1788.66 579.479C1790.28 580.587 1792.27 581.141 1794.62 581.141C1796.97 581.141 1798.95 580.587 1800.55 579.479C1802.17 578.354 1803.39 576.718 1804.21 574.57C1805.04 572.405 1805.46 569.755 1805.46 566.618Z' fill='black'/%3e %3cdefs%3e %3cclipPath id='clip0_72_232'%3e %3crect width='260' height='260' fill='white' transform='translate(660 400) rotate(-180)'/%3e %3c/clipPath%3e %3cclipPath id='clip1_72_232'%3e %3crect width='260' height='260' fill='white' transform='translate(140 400)'/%3e %3c/clipPath%3e %3c/defs%3e %3c/svg%3e",
			"src": "data:image/svg+xml,%3csvg width='1964' height='800' viewBox='0 0 1964 800' fill='none' xmlns='http://www.w3.org/2000/svg'%3e %3cpath d='M300 660C277.909 660 260 642.091 260 620C260 597.909 277.909 580 300 580L300 660ZM428.284 371.716L511.716 455.147L455.147 511.716L371.716 428.284L428.284 371.716ZM426.863 660L300 660L300 580L426.863 580L426.863 660ZM511.716 455.147C587.312 530.743 533.771 660 426.863 660L426.863 580C462.499 580 480.346 536.914 455.147 511.716L511.716 455.147Z' fill='%23FF0149'/%3e %3cpath d='M500 140C522.091 140 540 157.909 540 180C540 202.091 522.091 220 500 220L500 140ZM371.716 428.284L288.284 344.853L344.853 288.284L428.284 371.716L371.716 428.284ZM373.137 140L500 140L500 220L373.137 220L373.137 140ZM288.284 344.853C212.688 269.257 266.229 140 373.137 140L373.137 220C337.501 220 319.654 263.086 344.853 288.284L288.284 344.853Z' fill='%23FF0149'/%3e %3cpath d='M660 300C660 277.909 642.091 260 620 260C597.909 260 580 277.909 580 300L660 300ZM371.716 428.284L455.147 511.716L511.716 455.147L428.284 371.716L371.716 428.284ZM660 426.863L660 300L580 300L580 426.863L660 426.863ZM455.147 511.716C530.743 587.312 660 533.771 660 426.863L580 426.863C580 462.499 536.914 480.346 511.716 455.147L455.147 511.716Z' fill='black'/%3e %3cpath d='M140 500C140 522.091 157.909 540 180 540C202.091 540 220 522.091 220 500L140 500ZM428.284 371.716L344.853 288.284L288.284 344.853L371.716 428.284L428.284 371.716ZM140 373.137L140 500L220 500L220 373.137L140 373.137ZM344.853 288.284C269.257 212.688 140 266.229 140 373.137L220 373.137C220 337.501 263.086 319.654 288.284 344.853L344.853 288.284Z' fill='black'/%3e %3cg clip-path='url(%23clip0_72_232)'%3e %3cellipse cx='620' cy='180' rx='40' ry='40' transform='rotate(-180 620 180)' fill='%23FF0149'/%3e %3c/g%3e %3cg clip-path='url(%23clip1_72_232)'%3e %3cellipse cx='180' cy='620' rx='40' ry='40' fill='%23FF0149'/%3e %3c/g%3e %3cpath d='M1004.57 260C1020.65 260 1033.69 273.037 1033.69 289.12V482.8C1033.69 500.473 1019.36 514.8 1001.69 514.8H1000.41C990.827 514.8 981.753 510.51 975.675 503.108L858.24 360.1V485.68C858.24 501.763 845.203 514.8 829.12 514.8C813.037 514.8 800 501.763 800 485.68V292C800 274.327 814.327 260 832 260H833.619C843.213 260 852.3 264.304 858.378 271.727L975.448 414.7V289.12C975.448 273.037 988.485 260 1004.57 260Z' fill='black'/%3e %3cpath d='M1234.16 467.48C1247.22 467.48 1257.82 478.073 1257.82 491.14C1257.82 504.207 1247.22 514.8 1234.16 514.8H1097.69C1080.01 514.8 1065.69 500.473 1065.69 482.8V292C1065.69 274.327 1080.01 260 1097.69 260H1229.42C1242.49 260 1253.08 270.593 1253.08 283.66C1253.08 296.727 1242.49 307.32 1229.42 307.32H1124.29V362.648H1214.5C1227.17 362.648 1237.43 372.915 1237.43 385.58C1237.43 398.245 1227.17 408.512 1214.5 408.512H1124.29V467.48H1234.16Z' fill='black'/%3e %3cpath d='M1345.14 380.4L1392.9 476.576C1397.16 483.586 1404.78 487.864 1412.98 487.864C1421.19 487.864 1428.8 483.586 1433.06 476.576L1480.82 380.4V487.136C1480.82 502.414 1493.2 514.8 1508.48 514.8C1523.76 514.8 1536.15 502.414 1536.15 487.136V291.165C1536.15 273.953 1522.19 260 1504.98 260C1494.05 260 1483.92 265.724 1478.28 275.086L1412.98 406.4L1347.68 275.086C1342.04 265.724 1331.91 260 1320.98 260C1303.77 260 1289.82 273.953 1289.82 291.165V487.136C1289.82 502.414 1302.2 514.8 1317.48 514.8C1332.76 514.8 1345.14 502.414 1345.14 487.136V380.4Z' fill='black'/%3e %3cpath d='M1754.68 460.2H1636.38L1620.8 497.897C1616.57 508.127 1606.6 514.8 1595.53 514.8C1575.72 514.8 1562.48 494.405 1570.55 476.315L1655.1 286.615C1662.31 270.427 1678.38 260 1696.1 260C1713.8 260 1729.85 270.405 1737.08 286.566L1821.51 475.393C1829.79 493.905 1816.24 514.8 1795.97 514.8C1784.64 514.8 1774.43 507.973 1770.1 497.506L1754.68 460.2ZM1736.12 415.428L1695.72 317.876L1655.31 415.428H1736.12Z' fill='black'/%3e %3cpath d='M831.602 556.8C831.466 555.096 830.827 553.766 829.685 552.811C828.56 551.857 826.847 551.38 824.545 551.38C823.08 551.38 821.878 551.559 820.94 551.917C820.02 552.257 819.338 552.726 818.895 553.323C818.452 553.919 818.222 554.601 818.205 555.368C818.17 555.999 818.281 556.57 818.537 557.081C818.81 557.576 819.236 558.027 819.815 558.436C820.395 558.828 821.136 559.186 822.04 559.51C822.943 559.834 824.017 560.124 825.261 560.38L829.557 561.3C832.455 561.914 834.935 562.723 836.997 563.729C839.06 564.735 840.747 565.919 842.06 567.283C843.372 568.63 844.335 570.147 844.949 571.834C845.58 573.522 845.903 575.363 845.92 577.357C845.903 580.8 845.043 583.715 843.338 586.101C841.634 588.488 839.196 590.303 836.026 591.547C832.872 592.792 829.08 593.414 824.648 593.414C820.097 593.414 816.125 592.74 812.733 591.394C809.358 590.047 806.733 587.976 804.858 585.181C803 582.368 802.063 578.772 802.045 574.391H815.545C815.631 575.993 816.031 577.34 816.747 578.431C817.463 579.522 818.469 580.348 819.764 580.911C821.077 581.473 822.636 581.755 824.443 581.755C825.96 581.755 827.23 581.567 828.253 581.192C829.276 580.817 830.051 580.297 830.58 579.632C831.108 578.968 831.381 578.209 831.398 577.357C831.381 576.556 831.116 575.857 830.605 575.26C830.111 574.647 829.293 574.101 828.151 573.624C827.009 573.13 825.466 572.669 823.523 572.243L818.307 571.118C813.67 570.113 810.014 568.434 807.338 566.081C804.679 563.712 803.358 560.482 803.375 556.391C803.358 553.067 804.244 550.161 806.034 547.672C807.841 545.167 810.338 543.215 813.526 541.817C816.73 540.419 820.403 539.721 824.545 539.721C828.773 539.721 832.429 540.428 835.514 541.843C838.599 543.257 840.977 545.252 842.648 547.826C844.335 550.382 845.188 553.374 845.205 556.8H831.602Z' fill='black'/%3e %3cpath d='M998.339 551.891V540.436H1043.85V551.891H1028.1V592.8H1014.09V551.891H998.339Z' fill='black'/%3e %3cpath d='M1229.16 540.436H1243.37V573.982C1243.37 577.971 1242.42 581.422 1240.51 584.337C1238.62 587.235 1235.97 589.476 1232.58 591.061C1229.19 592.63 1225.25 593.414 1220.77 593.414C1216.25 593.414 1212.3 592.63 1208.91 591.061C1205.51 589.476 1202.87 587.235 1200.98 584.337C1199.1 581.422 1198.17 577.971 1198.17 573.982V540.436H1212.38V572.755C1212.38 574.374 1212.74 575.823 1213.46 577.101C1214.17 578.363 1215.16 579.351 1216.42 580.067C1217.7 580.783 1219.15 581.141 1220.77 581.141C1222.41 581.141 1223.85 580.783 1225.12 580.067C1226.38 579.351 1227.37 578.363 1228.08 577.101C1228.8 575.823 1229.16 574.374 1229.16 572.755V540.436Z' fill='black'/%3e %3cpath d='M1418.71 592.8H1398.56V540.436H1418.51C1423.89 540.436 1428.55 541.485 1432.47 543.581C1436.4 545.661 1439.44 548.661 1441.57 552.581C1443.72 556.485 1444.79 561.164 1444.79 566.618C1444.79 572.073 1443.73 576.76 1441.59 580.681C1439.46 584.584 1436.45 587.584 1432.54 589.681C1428.64 591.76 1424.03 592.8 1418.71 592.8ZM1412.78 580.732H1418.2C1420.79 580.732 1423 580.314 1424.82 579.479C1426.66 578.644 1428.06 577.203 1429.02 575.158C1429.99 573.113 1430.47 570.266 1430.47 566.618C1430.47 562.971 1429.98 560.124 1428.99 558.078C1428.02 556.033 1426.59 554.593 1424.69 553.757C1422.82 552.922 1420.52 552.505 1417.79 552.505H1412.78V580.732Z' fill='black'/%3e %3cpath d='M1614.18 540.436V592.8H1599.96V540.436H1614.18Z' fill='black'/%3e %3cpath d='M1820.08 566.618C1820.08 572.448 1818.95 577.365 1816.68 581.371C1814.42 585.36 1811.36 588.385 1807.5 590.448C1803.65 592.493 1799.36 593.516 1794.62 593.516C1789.84 593.516 1785.53 592.485 1781.68 590.422C1777.84 588.343 1774.79 585.309 1772.53 581.32C1770.28 577.314 1769.15 572.414 1769.15 566.618C1769.15 560.789 1770.28 555.88 1772.53 551.891C1774.79 547.885 1777.84 544.86 1781.68 542.814C1785.53 540.752 1789.84 539.721 1794.62 539.721C1799.36 539.721 1803.65 540.752 1807.5 542.814C1811.36 544.86 1814.42 547.885 1816.68 551.891C1818.95 555.88 1820.08 560.789 1820.08 566.618ZM1805.46 566.618C1805.46 563.482 1805.04 560.84 1804.21 558.692C1803.39 556.527 1802.17 554.891 1800.55 553.783C1798.95 552.658 1796.97 552.096 1794.62 552.096C1792.27 552.096 1790.28 552.658 1788.66 553.783C1787.06 554.891 1785.84 556.527 1785 558.692C1784.19 560.84 1783.78 563.482 1783.78 566.618C1783.78 569.755 1784.19 572.405 1785 574.57C1785.84 576.718 1787.06 578.354 1788.66 579.479C1790.28 580.587 1792.27 581.141 1794.62 581.141C1796.97 581.141 1798.95 580.587 1800.55 579.479C1802.17 578.354 1803.39 576.718 1804.21 574.57C1805.04 572.405 1805.46 569.755 1805.46 566.618Z' fill='black'/%3e %3cdefs%3e %3cclipPath id='clip0_72_232'%3e %3crect width='260' height='260' fill='white' transform='translate(660 400) rotate(-180)'/%3e %3c/clipPath%3e %3cclipPath id='clip1_72_232'%3e %3crect width='260' height='260' fill='white' transform='translate(140 400)'/%3e %3c/clipPath%3e %3c/defs%3e %3c/svg%3e",
			"size": 8
		}
	} } = $$props;

	let { nav = [
		{
			"link": {
				"label": "Features",
				"url": "/",
				"active": false
			}
		},
		{
			"link": {
				"label": "FAQ",
				"url": "/",
				"active": false
			}
		},
		{
			"link": {
				"label": "Community",
				"url": "/",
				"active": false
			}
		},
		{
			"link": {
				"label": "Team",
				"url": "",
				"active": false
			}
		}
	] } = $$props;

	let { cta = [] } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('nav' in $$props) $$invalidate(1, nav = $$props.nav);
		if ('cta' in $$props) $$invalidate(2, cta = $$props.cta);
	};

	return [logo, nav, cta, mobileNavOpen, click_handler, click_handler_1];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { logo: 0, nav: 1, cta: 2 });
	}
}

export default Component;
