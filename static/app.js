/* ParlTrack Canada: site-wide behaviour. Loaded once and cached by the browser. */
(function () {
  'use strict';
  var root = document.documentElement;

  function $(sel, ctx) { return (ctx || document).querySelector(sel); }
  function $$(sel, ctx) { return Array.prototype.slice.call((ctx || document).querySelectorAll(sel)); }
  function readJson(key, fallback) {
    try { var v = JSON.parse(localStorage.getItem(key)); return v === null || v === undefined ? fallback : v; } catch (e) { return fallback; }
  }
  function writeJson(key, value) { try { localStorage.setItem(key, JSON.stringify(value)); } catch (e) { /* storage blocked */ } }
  function getJson(url) {
    return fetch(url, { headers: { 'Accept': 'application/json' } }).then(function (r) { return r.json(); });
  }

  /* ---- Colour theme ---- */
  var themeBtn = $('#theme-toggle');
  if (themeBtn) {
    var syncLabel = function () {
      themeBtn.setAttribute('aria-label', root.classList.contains('dark') ? 'Switch to light theme' : 'Switch to dark theme');
    };
    syncLabel();
    themeBtn.addEventListener('click', function () {
      var dark = root.classList.toggle('dark');
      try { localStorage.setItem('parltrack.theme', dark ? 'dark' : 'light'); } catch (e) {}
      syncLabel();
    });
  }

  /* ---- Loading queues: a few requests at a time so Parliament's site is never hammered ---- */
  function queue(slots, load, width) {
    var next = 0;
    function worker() { if (next >= slots.length) { return; } load(slots[next++]).then(worker); }
    for (var i = 0; i < width; i++) { worker(); }
  }

  // Official summary text under "Proposed changes"
  queue($$('[data-summary-url]'), function (slot) {
    var target = $('[data-summary-text]', slot);
    return getJson(slot.getAttribute('data-summary-url'))
      .then(function (data) {
        target.textContent = data.summary || 'No official summary was found for this bill. Read the bill text for details.';
      })
      .catch(function () { target.textContent = 'The summary could not be loaded. Reload the page to try again.'; })
      .then(function () { slot.removeAttribute('aria-busy'); });
  }, 3);

  // Sponsor, party, recorded votes, and in-force note
  function show(el, text) { if (el && text) { el.textContent = text; el.hidden = false; } }
  function voteText(label, v) {
    if (!v) { return ''; }
    return label + ': ' + v.yeas + ' for, ' + v.nays + ' against' + (v.paired ? ', ' + v.paired + ' paired' : '');
  }
  queue($$('[data-meta-url]'), function (slot) {
    return getJson(slot.getAttribute('data-meta-url'))
      .then(function (d) {
        if (!d.ok) { return; }
        if (d.sponsor) {
          show($('[data-meta-sponsor]', slot),
               'Sponsor: ' + d.sponsor + (d.party ? ', ' + d.party : '') + (d.riding ? ' (' + d.riding + ')' : ''));
        }
        var votes = [voteText('Latest House vote', d.house_vote), voteText('Latest Senate vote', d.senate_vote)]
          .filter(Boolean).join(' · ');
        show($('[data-meta-vote]', slot), votes);
        show($('[data-meta-force]', slot), d.in_force ? 'In force: ' + d.in_force : '');
      })
      .catch(function () { /* the card is fine without it */ });
  }, 2);

  /* ---- Following bills: stars, "what changed since you followed it", and personal notes.
          Everything is kept in this browser only. ---- */
  var FOLLOW = 'parltrack.follow', BASE = 'parltrack.followBase', NOTES = 'parltrack.notes';

  function paintStar(btn, on) {
    btn.setAttribute('aria-pressed', on ? 'true' : 'false');
    btn.setAttribute('aria-label', (on ? 'Stop following ' : 'Follow ') + btn.getAttribute('data-follow'));
    var svg = $('svg', btn);
    if (svg) { svg.setAttribute('fill', on ? 'currentColor' : 'none'); }
  }

  function showChange(card, num, status) {
    var slot = $('[data-follow-change]', card);
    if (!slot) { return; }
    var base = readJson(BASE, {});
    var followed = readJson(FOLLOW, []).indexOf(num) !== -1;
    if (followed && base[num] && base[num] !== status) {
      slot.textContent = 'Since you followed it: ' + base[num] + ' → ' + status;
      slot.hidden = false;
    } else {
      slot.hidden = true;
    }
  }

  function showNote(card, num) {
    var slot = $('[data-note-show]', card);
    var text = readJson(NOTES, {})[num];
    if (!slot) { return; }
    if (text) { slot.textContent = 'Your note: ' + (text.length > 180 ? text.slice(0, 177) + '…' : text); slot.hidden = false; }
    else { slot.hidden = true; }
  }

  $$('[data-follow]').forEach(function (btn) {
    var num = btn.getAttribute('data-follow');
    var status = btn.getAttribute('data-status') || '';
    var card = btn.closest('[data-bill]') || document;
    var list = readJson(FOLLOW, []);
    var base = readJson(BASE, {});
    var on = list.indexOf(num) !== -1;
    if (on && base[num] === undefined && status) { base[num] = status; writeJson(BASE, base); }  // starred before tracking began
    paintStar(btn, on);
    showChange(card, num, status);
    showNote(card, num);
    btn.addEventListener('click', function () {
      var current = readJson(FOLLOW, []);
      var bases = readJson(BASE, {});
      var at = current.indexOf(num);
      if (at === -1) { current.push(num); if (status) { bases[num] = status; } }
      else { current.splice(at, 1); delete bases[num]; }
      writeJson(FOLLOW, current);
      writeJson(BASE, bases);
      paintStar(btn, at === -1);
      showChange(card, num, status);
    });
  });

  // Notes box on a bill's own page
  var noteBox = $('#bill-note');
  if (noteBox) {
    var noteNum = noteBox.getAttribute('data-bill');
    var noteStatus = $('#bill-note-status');
    noteBox.value = readJson(NOTES, {})[noteNum] || '';
    var timer = null;
    noteBox.addEventListener('input', function () {
      clearTimeout(timer);
      if (noteStatus) { noteStatus.textContent = 'Saving…'; }
      timer = setTimeout(function () {
        var notes = readJson(NOTES, {});
        if (noteBox.value.trim()) { notes[noteNum] = noteBox.value.slice(0, 1000); } else { delete notes[noteNum]; }
        writeJson(NOTES, notes);
        if (noteStatus) { noteStatus.textContent = 'Saved on this device only.'; }
      }, 500);
    });
  }

  /* ---- "Since you last checked" banner on the Active tab ---- */
  var banner = $('#visit-banner');
  if (banner) {
    var SNAP = 'parltrack.snapshot', STAMP = 'parltrack.snapshotAt';
    getJson(banner.getAttribute('data-url')).then(function (d) {
      var now = d.bills || {};
      var old = readJson(SNAP, null);
      if (!old) { writeJson(SNAP, now); writeJson(STAMP, new Date().toISOString()); return; }
      var followed = readJson(FOLLOW, []);
      var changes = [];
      Object.keys(now).forEach(function (num) {
        var cur = now[num];
        if (!old[num]) { changes.push({ num: num, kind: 'new', now: cur }); }
        else if (old[num].s !== cur.s) { changes.push({ num: num, kind: 'moved', from: old[num].s, now: cur }); }
      });
      if (!changes.length) { return; }
      changes.sort(function (a, b) {
        return (followed.indexOf(b.num) !== -1) - (followed.indexOf(a.num) !== -1) || (a.kind === 'moved' ? -1 : 1) - (b.kind === 'moved' ? -1 : 1);
      });

      var since = readJson(STAMP, '');
      var when = since ? new Date(since).toLocaleDateString(undefined, { month: 'long', day: 'numeric' }) : '';
      $('#visit-title').textContent = changes.length + (changes.length === 1 ? ' change' : ' changes') + (when ? ' since ' + when : ' since your last check');
      var list = $('#visit-list');
      changes.slice(0, 8).forEach(function (c) {
        var li = document.createElement('li');
        var a = document.createElement('a');
        a.href = '/bill/' + c.now.p + '/' + c.num;
        a.className = 'font-semibold underline decoration-maple-600/50 underline-offset-2 hover:text-maple-700';
        a.textContent = c.num;
        li.appendChild(a);
        var star = followed.indexOf(c.num) !== -1 ? ' ★ ' : ' ';
        li.appendChild(document.createTextNode(star + (c.kind === 'new' ? 'is new: ' + (c.now.t || '') : 'moved: ' + c.from + ' → ' + c.now.s)));
        list.appendChild(li);
      });
      if (changes.length > 8) { $('#visit-more').textContent = '+ ' + (changes.length - 8) + ' more'; }
      banner.hidden = false;
      $('#visit-dismiss').addEventListener('click', function () {
        writeJson(SNAP, now); writeJson(STAMP, new Date().toISOString()); banner.hidden = true;
      });
    }).catch(function () { /* no banner is better than a broken one */ });
  }

  /* ---- Glossary pop-up ---- */
  var glossary = {};
  try { glossary = JSON.parse($('#glossary-data').textContent); } catch (e) {}
  var sheet = $('#term-sheet');
  if (sheet) {
    var lastTrigger = null;
    var closeSheet = function () { sheet.hidden = true; if (lastTrigger) { lastTrigger.focus(); lastTrigger = null; } };
    document.addEventListener('click', function (e) {
      var t = e.target.closest('[data-term]');
      if (t && glossary[t.getAttribute('data-term')]) {
        var entry = glossary[t.getAttribute('data-term')];
        $('#term-title').textContent = entry.term;
        $('#term-text').textContent = entry.text;
        lastTrigger = t; sheet.hidden = false;
        $('#term-close').focus();
        return;
      }
      if (!sheet.hidden && !e.target.closest('#term-sheet [role=dialog]')) { closeSheet(); }
    });
    $('#term-close').addEventListener('click', closeSheet);
    document.addEventListener('keydown', function (e) { if (e.key === 'Escape' && !sheet.hidden) { closeSheet(); } });
  }

  /* ---- Share button ---- */
  $$('[data-share]').forEach(function (btn) {
    btn.addEventListener('click', function () {
      var data = { title: btn.getAttribute('data-title'), text: btn.getAttribute('data-text'), url: location.href };
      if (navigator.share) { navigator.share(data).catch(function () {}); return; }
      var label = $('[data-share-label]', btn);
      var done = function () { if (label) { var old = label.textContent; label.textContent = 'Link copied'; setTimeout(function () { label.textContent = old; }, 1800); } };
      if (navigator.clipboard) { navigator.clipboard.writeText(location.href).then(done, function () {}); }
    });
  });

  /* ---- Donut charts: hover, focus or tap a legend row or slice to highlight it ---- */
  $$('[data-donut]').forEach(function (chart) {
    var num = $('[data-c-num]', chart), lab = $('[data-c-lab]', chart);
    var base = { n: num.textContent, l: lab.textContent };
    function focusOn(idx) {
      var seg = $('.donut-seg[data-idx="' + idx + '"]', chart);
      var row = $('[data-leg][data-idx="' + idx + '"]', chart);
      $$('.donut-seg', chart).forEach(function (s) { s.removeAttribute('data-on'); });
      seg.setAttribute('data-on', ''); chart.setAttribute('data-active', '');
      num.textContent = row.getAttribute('data-count'); lab.textContent = row.getAttribute('data-label');
    }
    function reset() {
      chart.removeAttribute('data-active');
      $$('.donut-seg', chart).forEach(function (s) { s.removeAttribute('data-on'); });
      num.textContent = base.n; lab.textContent = base.l;
    }
    $$('[data-idx]', chart).forEach(function (el) {
      var idx = el.getAttribute('data-idx');
      el.addEventListener('mouseenter', function () { focusOn(idx); });
      el.addEventListener('focus', function () { focusOn(idx); });
      el.addEventListener('mouseleave', reset);
      el.addEventListener('blur', reset);
      el.addEventListener('click', function () { focusOn(idx); });
    });
  });

  /* ---- Member directories (House and Senate): live search, province filter, back to top ---- */
  var memberInput = $('#member-q');
  if (memberInput) {
    var province = $('#member-province');
    var statusEl = $('#member-status');
    var emptyEl = $('#member-empty');
    var sections = $$('[data-party-section]');
    var total = $$('[data-member]').length;
    var plain = function (s) { return s.normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase(); };
    var apply = function () {
      var term = plain(memberInput.value.trim()), prov = province.value, shown = 0;
      sections.forEach(function (sec) {
        var any = 0;
        $$('[data-member]', sec).forEach(function (li) {
          var ok = (!term || li.getAttribute('data-search').indexOf(term) !== -1) &&
                   (!prov || li.getAttribute('data-province') === prov);
          li.classList.toggle('hidden', !ok);
          if (ok) { any++; shown++; }
        });
        sec.classList.toggle('hidden', !any);
        $('[data-count]', sec).textContent = any;
        var chip = $('[data-chip="' + sec.id.replace('party-', '') + '"]');
        if (chip) {
          $('[data-chip-count]', chip).textContent = any;
          chip.classList.toggle('opacity-40', !any);
        }
      });
      statusEl.textContent = 'Showing ' + shown + ' of ' + total + ' ' + (statusEl.getAttribute('data-noun') || 'MPs');
      emptyEl.classList.toggle('hidden', shown > 0);
    };
    memberInput.addEventListener('input', apply);
    province.addEventListener('change', apply);
  }
  var toTop = $('#to-top');
  if (toTop) {
    window.addEventListener('scroll', function () {
      var showIt = window.scrollY > 700;
      toTop.classList.toggle('hidden', !showIt);
      toTop.classList.toggle('inline-flex', showIt);
    }, { passive: true });
    toTop.addEventListener('click', function () { window.scrollTo({ top: 0 }); });
  }

  /* ---- Party chart on the Statistics page: poll until it's ready, then reload once ---- */
  var pending = $('#party-pending');
  if (pending) {
    var pbar = $('#party-bar'), pcount = $('#party-count'), tries = 0;
    var poll = function () {
      tries++;
      getJson(pending.getAttribute('data-url'))
        .then(function (d) {
          if ((d.ready && d.status !== 'running') || d.status === 'error') { location.reload(); return; }
          if (d.total) {
            pbar.style.width = Math.max(4, Math.round(d.done / d.total * 100)) + '%';
            pcount.textContent = d.done + ' of ' + d.total + ' bills checked';
          }
          if (tries < 100) { setTimeout(poll, 3000); }
        })
        .catch(function () { if (tries < 100) { setTimeout(poll, 5000); } });
    };
    setTimeout(poll, 1500);
  }
})();
