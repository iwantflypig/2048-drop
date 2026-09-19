/* ============================================================
 * 2048 Drop — 俄罗斯方块式下落合并 2048
 * - 数字顶部生成，自动下落，过程中可左右移动 / 加速 / 直落
 * - 落地后与下方相同数字合并，**无限连锁**直至不能合并
 * - 方块用持久化 DOM + CSS 过渡，移动全程动画流畅
 * - 满列但顶部数字相同 → 仍可落入并合并（救活机制）
 * ============================================================ */
(function () {
  'use strict';

  /* ===== 常量 ===== */
  var ROWS = 8;
  var COLS = 7;
  var TARGETS = [128, 256, 512, 1024, 2048, 4096, 8192];
  var FALL_MS = 600;      // 自动下落一格
  var SOFT_MS = 90;       // 按住↓加速（≈7倍速）
  var SAVE_KEY = 'drop2048.save';
  var BEST_KEY = 'drop2048.best';
  var START_COL = 3;      // 始终在中间列生成
  var SPEED = 1;          // 动画速度倍率（测试时可调快）
  var soundOn = true;     // 音效开关

  /* ===== 音效系统（Web Audio API，无需外部文件）===== */
  var audioCtx = null;
  var musicTimer = null;
  var musicNote = 0;
  function ensureAudio() {
    if (!audioCtx) {
      try { audioCtx = new (window.AudioContext || window.webkitAudioContext)(); } catch(e) { audioCtx = null; }
    }
    if (audioCtx && audioCtx.state === 'suspended') audioCtx.resume();
    return audioCtx;
  }
  function beep(freq, dur, vol, type) {
    if (!soundOn) return;
    try {
      var ctx = ensureAudio();
      if (!ctx) return;
      var osc = ctx.createOscillator();
      var gain = ctx.createGain();
      osc.type = type || 'sine';
      osc.frequency.value = freq;
      gain.gain.setValueAtTime(vol || 0.08, ctx.currentTime);
      gain.gain.exponentialRampToValueAtTime(0.001, ctx.currentTime + dur);
      osc.connect(gain).connect(ctx.destination);
      osc.start(); osc.stop(ctx.currentTime + dur);
    } catch(e) { /* ignore audio errors in test env */ }
  }
  function playSound(type) {
    if (!soundOn) return;
    if (type === 'merge') beep(523 + Math.random()*200, 0.12, 0.1, 'triangle');
    else if (type === 'drop') beep(220, 0.08, 0.06, 'sine');
    else if (type === 'over') { beep(200,0.3,0.15,'sawtooth'); setTimeout(function(){beep(150,0.4,0.12,'sawtooth');},200); }
  }
  var musicNotes = [262,294,330,349,392,349,330,294];
  var musicGain = null;
  var musicOsc = null;
  function startMusic() {
    stopMusic();
    if (!soundOn) return;
    try {
      var ctx = ensureAudio();
      if (!ctx) return;
      musicGain = ctx.createGain();
      musicGain.gain.value = 0.03;
      musicGain.connect(ctx.destination);
      musicOsc = ctx.createOscillator();
      musicOsc.type = 'sine';
      musicOsc.connect(musicGain);
      musicOsc.start();
      musicNote = 0;
      musicTimer = setInterval(function () {
        if (!soundOn || !musicOsc) { stopMusic(); return; }
        musicOsc.frequency.setValueAtTime(musicNotes[musicNote % musicNotes.length], ctx.currentTime);
        musicNote++;
      }, 400);
    } catch(e) { /* ignore */ }
  }
  function stopMusic() {
    if (musicTimer) { clearInterval(musicTimer); musicTimer = null; }
    if (musicOsc) { try { musicOsc.stop(); } catch(e){} musicOsc = null; }
    musicGain = null;
  }
  function toggleSound() {
    soundOn = !soundOn;
    $('soundBtn').textContent = soundOn ? '🔊' : '🔇';
    try { localStorage.setItem('drop2048.sound', soundOn ? '1' : '0'); } catch(e){}
    if (soundOn) startMusic(); else stopMusic();
  }
  function resumeAudioOnGesture() {
    if (audioCtx && audioCtx.state === 'suspended') audioCtx.resume();
    if (soundOn && !musicOsc) startMusic();
  }

  /* ===== 状态 ===== */
  var board = [];         // 每格: null 或 {v, el}
  var score = 0, best = 0, moves = 0, merges = 0, maxTile = 0;
  var cur = 2, next = 4;  // 当前 / 下一个数字
  var curTile = null;     // 正在下落的方块对象 {v, el}
  var fr = -1, fc = START_COL;
  var fy = 0;             // 连续下落的浮点行位置（逐帧渲染插值用）
  var phase = 'falling';  // falling | resolving | paused | over
  var softDrop = false;
  var zoom = 1;
  var reached = {};
  var runId = 0;          // 动画链代际号：newGame 使旧链失效
  var comboHideTimer = 0;

  /* ===== DOM ===== */
  function $(id) { return document.getElementById(id); }
  var boardEl, cellsEl, tilesEl, ghostEl, fallEl, dangerEl, colHiEl;
  var scoreEl, bestEl, maxEl, movesEl, mergesEl, comboEl, nextEl;
  var popupEl, comboPopEl, overOv;

  /* ===== 工具 ===== */
  function delay(ms) { return new Promise(function (r) { setTimeout(r, ms * SPEED); }); }
  function alive(id) { return id === runId; }
  function cls(v) { return v > 8192 ? 'csuper' : 'c' + v; }

  var mem = {};
  var store = {
    get: function (k) { try { return localStorage.getItem(k); } catch (e) { return (k in mem) ? mem[k] : null; } },
    set: function (k, v) { try { localStorage.setItem(k, v); } catch (e) { mem[k] = v; } },
    del: function (k) { try { localStorage.removeItem(k); } catch (e) { delete mem[k]; } }
  };

  /* ===== 布局公式（格子与方块共用，保证同尺寸）===== */
  var M = { w: 448, h: 784, gap: 4, cw: 50, ch: 50 };
  function metrics() {
    var w = boardEl.clientWidth || 448;
    var h = boardEl.clientHeight || Math.round(w * ROWS / COLS);
    var gap = Math.max(2, Math.round(Math.min(w / COLS, h / ROWS) * 0.07));
    M = { w: w, h: h, gap: gap, cw: (w - gap * (COLS - 1)) / COLS, ch: (h - gap * (ROWS - 1)) / ROWS };
    return M;
  }
  function rect(row, col) {
    return { x: col * (M.cw + M.gap), y: row * (M.ch + M.gap), w: M.cw, h: M.ch };
  }
  function fontOf(v) {
    var base = Math.min(M.cw, M.ch);
    var f = v < 100 ? 0.46 : v < 1000 ? 0.38 : 0.30;
    return Math.round(base * f) + 'px';
  }
  function setBox(el, r) {
    el.style.left = r.x + 'px';
    el.style.top = r.y + 'px';
    el.style.width = r.w + 'px';
    el.style.height = r.h + 'px';
  }

  /* ===== 棋盘判定 ===== */
  function colOpen(c) {
    // 列可进入：顶部为空，或顶部数字与当前相同（可合并救活）
    var top = board[0][c];
    return top === null || top.v === cur;
  }
  function canGo(r, c) {
    if (c < 0 || c >= COLS) return false;
    if (r >= ROWS) return false;
    if (r < 0) return colOpen(c);   // 顶行上方：只能移到可进入的列
    return board[r][c] === null;
  }
  function colHeight(c) {
    for (var r = 0; r < ROWS; r++) if (board[r][c] !== null) return ROWS - r;
    return 0;
  }

  /* ===== 方块元素 ===== */
  function refreshTileEl(t) {
    t.el.textContent = t.v;
    t.el.className = 'tileBox ' + cls(t.v);
    t.el.style.fontSize = fontOf(t.v);
  }
  function newTileEl(t, row, col) {
    var el = document.createElement('div');
    t.el = el;
    refreshTileEl(t);
    el.style.transition = 'none';
    setBox(el, rect(row, col));
    tilesEl.appendChild(el);
    return el;
  }

  /* ===== 智能数字生成（盘面分析 + 渐进难度 + 随机性）===== */
  function genTile() {
    // 收集盘面信息
    var counts = {}, totalTiles = 0;
    for (var r = 0; r < ROWS; r++) {
      for (var c = 0; c < COLS; c++) {
        if (board[r][c]) {
          counts[board[r][c].v] = (counts[board[r][c].v] || 0) + 1;
          totalTiles++;
        }
      }
    }

    // 确定可生成的数字范围（随最高数字渐进解锁）
    var candidates = [2, 4];                 // 始终可生成
    if (maxTile >= 32)  candidates.push(8);
    if (maxTile >= 128) candidates.push(16);
    if (maxTile >= 256) candidates.push(32);
    if (maxTile >= 512) candidates.push(64);

    // 基础概率分布：2 始终最高，但整体曲线更陡（难度更高）
    // 随 maxTile 增大，概率曲线右移更快（大数字更早变多）
    var baseWeights = { 2: 35, 4: 28, 8: 18, 16: 12, 32: 5, 64: 2 };

    // 根据 maxTile 调整：越高则大数字基础权重越大（更早解锁大数字）
    var shift = 0;
    if (maxTile >= 32)  shift = 1;   // 32就提前解锁8的权重
    if (maxTile >= 64)  shift = 2;
    if (maxTile >= 128) shift = 3;
    if (maxTile >= 256) shift = 4;
    if (maxTile >= 512) shift = 5;

    var weights = {};
    for (var i = 0; i < candidates.length; i++) {
      var v = candidates[i];
      var w = baseWeights[v] || 1;

      // 进度越高，大数字权重提升
      var idx = candidates.indexOf(v);
      w = Math.max(1, w + (idx - 0) * shift * 2);

      // 盘面影响（轻度）：如果这个数字在盘面上存在，小幅提升概率
      // 使用平方根抑制，避免某个数字过多时完全垄断
      if (counts[v]) {
        w += Math.sqrt(counts[v]) * 3;  // 平方根抑制：2个+4.2，4个+6，8个+8.5
      }

      // 连锁激励：盘面上恰好有 2 个相邻可能时，略微提升
      // （但不强制，保持随机性）
      if (counts[v] >= 2 && counts[v] <= 4) {
        w *= 1.2;
      }

      // 2 的数字永远不低于 30%，保证游戏可玩性
      if (v === 2) w = Math.max(w, 30);

      weights[v] = w;
    }

    // 加权随机选择
    var totalW = 0;
    for (var v in weights) totalW += weights[v];

    var r = Math.random() * totalW;
    var cum = 0;
    for (var i = 0; i < candidates.length; i++) {
      var v = candidates[i];
      cum += weights[v];
      if (r <= cum) return v;
    }

    return 2; // 兜底
  }

  /* ===== 静态渲染 ===== */
  function renderCells() {
    cellsEl.innerHTML = '';
    for (var r = 0; r < ROWS; r++) {
      for (var c = 0; c < COLS; c++) {
        var d = document.createElement('div');
        d.className = 'cell';
        d.style.transition = 'none';
        setBox(d, rect(r, c));
        cellsEl.appendChild(d);
      }
    }
  }

  function updateHUD() {
    scoreEl.textContent = score;
    bestEl.textContent = best;
    maxEl.textContent = maxTile > 0 ? maxTile : '-';
    movesEl.textContent = moves;
    mergesEl.textContent = merges;
  }

  function renderNext() {
    nextEl.textContent = next;
    nextEl.className = cls(next);
    nextEl.style.fontSize = fontOf(next);
  }

  function updateDanger() {
    var d = false;
    for (var c = 0; c < COLS; c++) if (colHeight(c) >= ROWS - 2) d = true;
    dangerEl.classList.toggle('on', d);
  }

  function positionDanger() {
    var y = 2 * (M.ch + M.gap) - M.gap;
    dangerEl.style.top = y + 'px';
  }

  /* ===== 下落方块定位 ===== */
  function placeFall(instant) {
    if (phase !== 'falling' || !curTile) {
      fallEl.style.display = 'none';
      ghostEl.style.display = 'none';
      return;
    }
    var el = curTile.el;
    // top 由主循环逐帧插值控制，这里只负责 left 的平滑
    el.style.transition = instant ? 'none' : 'left 90ms ease';
    el.style.display = 'flex';
    el.style.zIndex = 6;
    var r = rect(fr, fc);
    r.y = fy * (M.ch + M.gap);          // 浮点行位置，保证连续滑动
    setBox(el, r);
    el.style.fontSize = fontOf(curTile.v);
    updateGhost();
  }

  // 幽灵落点 & 满列可合并提示（只更新辅助元素，不动下落方块）
  function updateGhost() {
    if (!curTile) { ghostEl.style.display = 'none'; return; }
    var g = fr;
    while (g + 1 < ROWS && board[g + 1][fc] === null) g++;
    clearMergeHint();
    ghostEl.style.display = 'none';
    if (g >= 0 && g !== fr) {
      ghostEl.style.display = 'block';
      setBox(ghostEl, rect(g, fc));
    } else if (board[0][fc] !== null && board[0][fc].v === curTile.v) {
      board[0][fc].el.classList.add('willMerge');
    }
  }

  var mergeHintEl = null;
  function clearMergeHint() {
    if (mergeHintEl) { mergeHintEl.classList.remove('willMerge'); mergeHintEl = null; }
    var prev = tilesEl.querySelector('.willMerge');
    if (prev) prev.classList.remove('willMerge');
  }

  /* ===== 弹出提示 ===== */
  function popup(text) {
    popupEl.textContent = text;
    popupEl.classList.add('on');
    var id = runId;
    setTimeout(function () { if (id === runId) popupEl.classList.remove('on'); }, 1300 * SPEED);
  }
  function showCombo(n) {
    comboPopEl.textContent = 'COMBO ×' + n;
    comboPopEl.classList.remove('on');
    void comboPopEl.offsetWidth;
    comboPopEl.classList.add('on');
    comboEl.textContent = 'COMBO ×' + n;
    clearTimeout(comboHideTimer);
    comboHideTimer = setTimeout(function () { comboEl.textContent = ''; }, 2200);
  }

  /* ===== 下落控制 ===== */
  function moveH(d) {
    if (phase !== 'falling' || !curTile) return;
    var nc = fc + d;
    if (!canGo(fr, nc)) return;
    fc = nc;
    // 新列更矮时收紧 fy，防止方块回弹跳上 去
    var R2 = fr;
    while (R2 + 1 < ROWS && board[R2 + 1][fc] === null) R2++;
    if (fy > R2) fy = R2;
    placeFall();
  }

  function hardDrop() {
    if (phase !== 'falling' || !curTile) return;
    if (fr < 0) {
      if (colOpen(fc)) { fy = 0; land(-1); }
      return;
    }
    if (board[fr][fc] !== null) { fy = fr; land(-1); return; }  // 顶部贴入合并
    while (canGo(fr + 1, fc)) fr++;
    fy = fr;
    placeFall(true);
    land(fr);
  }

  // 点击列 = 明确指令：跳到该列顶部再直落
  function dropIntoColumn(col) {
    if (phase !== 'falling' || !curTile) return;
    if (col < 0 || col >= COLS) return;
    var top = board[0][col];
    if (top !== null && top.v !== curTile.v) return;  // 该列不可进入
    fc = col;
    fr = (board[0][fc] !== null) ? -1 : 0;  // 满顶可合并列 → 从顶贴入
    fy = fr;
    placeFall(true);
    hardDrop();
  }

  /* ===== 落地 → 无限连锁合并（下/左/右十字） ===== */
  function land(row) {
    var id = runId;
    phase = 'resolving';
    lastChainTick = Date.now();
    moves++;
    var col = fc;
    var t = curTile;
    curTile = null;
    ghostEl.style.display = 'none';
    clearMergeHint();

    var el = t.el;
    el.style.zIndex = 5;
    if (row >= 0) {
      board[row][col] = t;
      el.style.transition = 'none';
      setBox(el, rect(row, col));
      refreshTileEl(t);
      el.classList.add('land');
      setTimeout(function () { if (alive(id)) el.classList.remove('land'); }, 220 * SPEED);
    } else {
      // 满列合并进入：t 贴在顶行，与顶行方块重叠并合并
      board[0][col] = t;
      row = 0;
      el.style.transition = 'none';
      el.style.zIndex = 6;
      setBox(el, rect(0, col));
    }
    updateHUD();
    updateDanger();
    delay(140).then(function () { if (alive(id)) mergeChain(row, col, t, id); })
      .catch(function (e) { chainError(e, id); });
  }

  // 列内重力沉降（带下落动画，同步更新 board）
  function settleColAnim(c) {
    var stack = [];
    for (var r = 0; r < ROWS; r++) if (board[r][c]) stack.push(board[r][c]);
    for (var r2 = 0; r2 < ROWS; r2++) board[r2][c] = null;
    var base = ROWS - stack.length;
    for (var i = 0; i < stack.length; i++) {
      var t2 = stack[i];
      var nr = base + i;
      t2.el.style.transition = 'top 150ms ease-in';
      setBox(t2.el, rect(nr, c));
      board[nr][c] = t2;
    }
  }

  // 找到所有相邻的相同数字（4方向洪水填充）
  function findGroup(r, c, val) {
    var group = [], visited = {}, q = [{r:r,c:c}];
    visited[r+','+c] = true;
    while (q.length) {
      var cur = q.shift();
      group.push(cur);
      var dirs = [[1,0],[-1,0],[0,1],[0,-1]];
      for (var i = 0; i < 4; i++) {
        var nr = cur.r+dirs[i][0], nc = cur.c+dirs[i][1];
        if (nr>=0 && nr<ROWS && nc>=0 && nc<COLS && !visited[nr+','+nc]) {
          var n = board[nr][nc];
          if (n && n.v === val) { visited[nr+','+nc] = true; q.push({r:nr,c:nc}); }
        }
      }
    }
    return group;
  }

  /* ===== 落地 → 合并所有相邻相同数字 → 继续连锁 ===== */
  function mergeChain(row, col, t, id) {
    var chain = 0, gained = 0;

    function step() {
      if (!alive(id)) return Promise.resolve();
      var group = findGroup(row, col, t.v);
      if (group.length < 2) return Promise.resolve();

      var count = group.length;
      var newVal = t.v * Math.pow(2, count - 1);
      var mergeGain = t.v * (Math.pow(2, count) - 2);
      var colsAffected = {};
      for (var i = 0; i < group.length; i++) colsAffected[group[i].c] = true;

      // 收集非中心方块的引用和坐标（动画前获取，避免被覆盖后丢失）
      var absorbed = [];
      for (var i = 0; i < group.length; i++) {
        var g = group[i];
        if (g.r === row && g.c === col) continue;
        absorbed.push({r: g.r, c: g.c, obj: board[g.r][g.c]});
      }

      // 动画：非中心方块滑向中心并消失
      for (var i = 0; i < absorbed.length; i++) {
        var other = absorbed[i];
        board[other.r][other.c] = null;
        if (other.obj && other.obj.el) {
          other.obj.el.classList.add('absorbed');
          other.obj.el.style.transition = 'all 130ms ease-in';
          setBox(other.obj.el, rect(row, col));
        }
      }

      gained += mergeGain;
      merges += count - 1;
      chain++;
      lastChainTick = Date.now();

      return delay(180).then(function () {
        if (!alive(id)) return;
        // 清除被吸收的 DOM
        for (var i = 0; i < absorbed.length; i++) {
          if (absorbed[i].obj && absorbed[i].obj.el) absorbed[i].obj.el.remove();
        }

        t.v = newVal;
        board[row][col] = t;
        refreshTileEl(t);
        t.el.style.transition = 'none';
        setBox(t.el, rect(row, col));
        void t.el.offsetWidth;
        t.el.classList.add('merge');
        setTimeout(function () { if (alive(id)) t.el.classList.remove('merge'); }, 260 * SPEED);
        if (t.v > maxTile) { maxTile = t.v; onMaxTile(t.v); }
        updateHUD();
        updateDanger();
        playSound('merge');

        for (var c in colsAffected) settleColAnim(c);
        return delay(160).then(function () {
          // 重力沉降后 t 的位置可能变了，重新定位
          for (var r2 = 0; r2 < ROWS; r2++) {
            for (var c2 = 0; c2 < COLS; c2++) {
              if (board[r2][c2] === t) { row = r2; col = c2; break; }
            }
          }
          step();
        });
      });
    }

    step().then(function () {
      if (!alive(id)) return;
      if (gained > 0) {
        var bonus = chain > 1 ? Math.floor(gained * 0.25 * (chain - 1)) : 0;
        score += gained + bonus;
        if (chain > 1) showCombo(chain);
      }
      if (score > best) { best = score; store.set(BEST_KEY, String(best)); }
      updateHUD();
      delay(90).then(function () { if (alive(id)) spawnNext(); });
    }).catch(function (e) { chainError(e, id); });
  }

  // 合并链异常恢复：记录 + 强制走完流程，保证游戏不卡死、结束有提示
  function chainError(e, id) {
    if (!alive(id)) return;
    console.error('merge chain error:', e);
    if (checkGameOver()) endGame();
    else spawnNext();
  }

  function onMaxTile(v) {
    if (v >= 128) popup('NEW TILE! ' + v);
    if (v === 2048 && !reached['2048']) {
      reached['2048'] = true;
      popup('2048 REACHED!');
    }
  }

  /* ===== 生成下一个 / 游戏结束 ===== */
  function openSpawnCol() {
    // 优先 START_COL，找顶部为空的列；退而求其次找顶部可合并的列
    var mergeCol = -1;
    for (var d = 0; d < COLS; d++) {
      var c1 = START_COL + Math.ceil(d / 2) * (d % 2 ? 1 : -1);
      if (c1 < 0 || c1 >= COLS) continue;
      if (board[0][c1] === null) return c1;
      if (mergeCol < 0 && board[0][c1].v === cur) mergeCol = c1;
    }
    return mergeCol; // -1 = 彻底无路（Game Over）
  }

  function spawnNext() {
    // 看门狗兜底
    if (curTile && curTile.el && phase === 'resolving') curTile.el.remove();
    cur = next;
    next = genTile();
    fc = START_COL;
    if (board[0][fc] === null) { fr = 0; fy = 0; }
    else { fr = -1; fy = 0; }
    curTile = { v: cur, el: null };
    newTileEl(curTile, 0, fc);
    curTile.el.style.boxShadow = '0 5px 14px rgba(0,0,0,0.3)';
    renderNext();
    updateHUD();
    if (checkGameOver()) { endGame(); return; }
    // 新数字在顶部停留一段时间，等合并动画完全结束后再开始下落
    setTimeout(function () {
      phase = 'falling';
      placeFall(true);
    }, 300);
    saveGame();
  }

  function checkGameOver() {
    for (var c = 0; c < COLS; c++) {
      if (board[0][c] !== null) return true;  // 任意一列顶行被堵 → Game Over
    }
    return false;
  }

  function endGame() {
    phase = 'over';
    if (curTile && curTile.el) curTile.el.style.display = 'none';
    curTile = null;
    ghostEl.style.display = 'none';
    stopMusic();
    playSound('over');
    if (score > best) { best = score; store.set(BEST_KEY, String(best)); }
    $('finalScore').textContent = score;
    $('finalMax').textContent = maxTile;
    $('overTitle').textContent = reached['2048'] ? '2048 已达成' : 'GAME OVER';
    $('overMsg').textContent = '没有可以落入的列了';
    overOv.classList.add('on');
    updateHUD();
    store.del(SAVE_KEY);
  }

  /* ===== 新游戏 / 存档 ===== */
  function newGame() {
    runId++;
    board = [];
    for (var r = 0; r < ROWS; r++) board.push(new Array(COLS).fill(null));
    tilesEl.innerHTML = '';
    score = 0; moves = 0; merges = 0; maxTile = 0;
    reached = {};
    cur = genTile();
    next = genTile();
    softDrop = false;
549|    overOv.classList.remove('on');
    comboEl.textContent = '';
    updateHUD();
    renderNext();
    fc = START_COL;
    fr = 0; fy = 0;                       // 直接出现在最顶行
    curTile = { v: cur, el: null };
    newTileEl(curTile, 0, fc);
    phase = 'falling';
    lastChainTick = Date.now();
    placeFall(true);
    store.del(SAVE_KEY);
  }

  function saveGame() {
    // 只存数值，恢复时重建元素
    var b = [];
    for (var r = 0; r < ROWS; r++) {
      var row = [];
      for (var c = 0; c < COLS; c++) row.push(board[r][c] ? board[r][c].v : 0);
      b.push(row);
    }
    store.set(SAVE_KEY, JSON.stringify({
      board: b, score: score, moves: moves, merges: merges,
      maxTile: maxTile, cur: cur, next: next, reached: reached
    }));
  }

  function loadState(state) {
    // 由数值棋盘重建游戏（newGame 基础上覆盖）
    runId++;
    board = [];
    tilesEl.innerHTML = '';
    for (var r = 0; r < ROWS; r++) {
      var row = new Array(COLS).fill(null);
      for (var c = 0; c < COLS; c++) {
        var v = state.board[r][c];
        if (v) {
          var t = { v: v, el: null };
          newTileEl(t, r, c);
          row[c] = t;
        }
      }
      board.push(row);
    }
    score = state.score | 0; moves = state.moves | 0; merges = state.merges | 0;
    maxTile = state.maxTile | 0;
    cur = state.cur || 2; next = state.next || genTile();
    reached = state.reached || {};
    fc = START_COL;
    fr = 0; fy = 0;                       // 直接出现在最顶行
    curTile = { v: cur, el: null };
    newTileEl(curTile, 0, fc);
    phase = 'falling';
    lastChainTick = Date.now();
    renderNext();
    updateHUD();
    updateDanger();
    if (checkGameOver()) { endGame(); return false; }
    placeFall(true);
    return true;
  }

  function tryResume() {
    var raw = store.get(SAVE_KEY);
    if (!raw) return false;
    try {
      var s = JSON.parse(raw);
      if (!s || !Array.isArray(s.board) || s.board.length !== ROWS) return false;
      return loadState(s);
    } catch (e) { return false; }
  }

  /* ===== 缩放 ===== */
  function applyZoom() {
    boardEl.style.transform = 'scale(' + zoom + ')';
    boardEl.style.transformOrigin = 'top center';
  }
  function zoomIn() { zoom = Math.min(1.5, +(zoom + 0.1).toFixed(2)); applyZoom(); }
  function zoomOut() { zoom = Math.max(0.6, +(zoom - 0.1).toFixed(2)); applyZoom(); }

  /* ===== 主循环：连续下落（逐帧像素插值，无格跳感） ===== */
  var lastT = 0;
  var lastChainTick = 0;   // 合并链心跳（看门狗用）
  function frame(t) {
    if (!lastT) lastT = t;
    var dt = Math.min(100, t - lastT);
    lastT = t;
    if (phase === 'falling' && curTile) {
      var rowPx = M.ch + M.gap;
      var speed = 1 / (softDrop ? SOFT_MS : FALL_MS);   // 行/毫秒（fy 是行索引）
      fy += speed * dt;

      // 计算当前列的最终停靠行 R（列已沉降，无空洞）
      var R = fr;
      while (R + 1 < ROWS && board[R + 1][fc] === null) R++;
      var target = (R >= 0) ? R : 0;   // 满列合并进入时贴到顶行

      if (fy >= target) {
        fy = target;
        fr = R;
        land(R);                       // R=-1 → 顶部合并进入
      } else {
        fr = Math.floor(fy + 1e-6);    // 当前所在行（供左右移动碰撞判定）
        curTile.el.style.top = (fy * rowPx) + 'px';
      }
    } else if (phase === 'resolving') {
      // 看门狗：合并链心跳超时（异常中断/卡死）→ 强制走完流程，
      // 保证游戏不会无提示地卡在 resolving
      if (Date.now() - lastChainTick > 2500) {
        console.warn('merge chain watchdog fired, forcing recovery');
        runId++;                       // 掐掉所有挂起的链回调
        if (checkGameOver()) { endGame(); }
        else { phase = 'falling'; spawnNext(); }
      }
    }
    requestAnimationFrame(frame);
  }

  /* ===== 事件 ===== */
  function colFromEvent(e) {
    var rectB = boardEl.getBoundingClientRect();
    var x = (e.touches && e.touches.length) ? e.touches[0].clientX - rectB.left : e.clientX - rectB.left;
    var col = Math.floor(x / (rectB.width / COLS));
    return Math.max(0, Math.min(COLS - 1, col));
  }

  function bindEvents() {
    boardEl.addEventListener('click', function (e) { dropIntoColumn(colFromEvent(e)); });
    boardEl.addEventListener('touchstart', function (e) {
      if (phase !== 'falling') return;
      e.preventDefault();
      dropIntoColumn(colFromEvent(e));
    }, { passive: false });
    // 防止页面滚动 + iOS 回弹
    document.addEventListener('touchmove', function (e) { if (e.target.closest('#board, .touchpad, #gameArea')) e.preventDefault(); }, { passive: false });
    document.addEventListener('gesturestart', function (e) { e.preventDefault(); });
    document.body.addEventListener('touchmove', function (e) { e.preventDefault(); }, { passive: false });

    boardEl.addEventListener('mousemove', function (e) {
      var c = colFromEvent(e);
      colHiEl.style.display = 'block';
      colHiEl.style.transition = 'none';
      setBox(colHiEl, { x: c * (M.cw + M.gap), y: 0, w: M.cw, h: M.h });
    });
    boardEl.addEventListener('mouseleave', function () { colHiEl.style.display = 'none'; });

    document.addEventListener('keydown', function (e) {
      var k = e.key;
      if (k === 'ArrowLeft' || k === 'a' || k === 'A') { e.preventDefault(); moveH(-1); }
      else if (k === 'ArrowRight' || k === 'd' || k === 'D') { e.preventDefault(); moveH(1); }
      else if (k === 'ArrowDown' || k === 's' || k === 'S') { e.preventDefault(); softDrop = true; }
      else if (k === ' ') { e.preventDefault(); if (!e.repeat) hardDrop(); }
      else if (k >= '1' && k <= '8') { dropIntoColumn(parseInt(k, 10) - 1); }
      else if (k === 'n' || k === 'N') newGame();
      else if (k === '+' || k === '=') zoomIn();
      else if (k === '-' || k === '_') zoomOut();
    });
    document.addEventListener('keyup', function (e) {
      if (e.key === 'ArrowDown' || e.key === 's' || e.key === 'S') softDrop = false;
    });

    function press(id, down, up) {
      var el = $(id);
      el.addEventListener('touchstart', function (e) { e.preventDefault(); down(); }, { passive: false });
      el.addEventListener('mousedown', down);
      if (up) {
        el.addEventListener('touchend', function (e) { e.preventDefault(); up(); }, { passive: false });
        el.addEventListener('mouseup', up);
      }
    }
    press('btnLeft', function () { moveH(-1); });
    press('btnRight', function () { moveH(1); });
    press('btnSoft', function () { softDrop = true; }, function () { softDrop = false; });
    $('btnNew').addEventListener('click', newGame);
    $('soundBtn').addEventListener('click', toggleSound);
    $('btnOverNew').addEventListener('click', newGame);

    window.addEventListener('resize', relayout);
    document.addEventListener('visibilitychange', function () {
    });
  }

  function relayout() {
    metrics();
    renderCells();
    // 重排所有方块（无过渡）
    for (var r = 0; r < ROWS; r++) {
      for (var c = 0; c < COLS; c++) {
        var t = board[r][c];
        if (t) {
          t.el.style.transition = 'none';
          refreshTileEl(t);
          setBox(t.el, rect(r, c));
        }
      }
    }
    if (curTile) {
      curTile.el.style.transition = 'none';
      refreshTileEl(curTile);
      var rF = rect(fr, fc);
      rF.y = fy * (M.ch + M.gap);
      setBox(curTile.el, rF);
    }
    positionDanger();
    placeFall(true);
  }

  /* ===== 初始化 ===== */
  function init() {
    boardEl = $('board'); cellsEl = $('cells'); tilesEl = $('tiles');
    ghostEl = $('ghost'); fallEl = $('fallTile'); dangerEl = $('danger'); colHiEl = $('colHi');
    scoreEl = $('score'); bestEl = $('best'); maxEl = $('maxTile');
    movesEl = $('moves'); mergesEl = $('merges'); comboEl = $('combo');
    nextEl = $('nextTile');
    popupEl = $('popup'); comboPopEl = $('comboPop');
    overOv = $('overOverlay');

    best = parseInt(store.get(BEST_KEY) || '0', 10) || 0;
    soundOn = (localStorage.getItem('drop2048.sound') || '1') === '1';

    board = [];
    for (var r = 0; r < ROWS; r++) board.push(new Array(COLS).fill(null));

    // 确保 DOM 布局完成后再初始化，避免尺寸为 0 导致游戏无法启动
    requestAnimationFrame(function () {
      metrics();
      renderCells();
      positionDanger();
      updateHUD();
      renderNext();

      if (!tryResume()) newGame();
      bindEvents();
      // 首次交互后启动音频（解决浏览器自动播放限制）
      var startAudio = function () {
        resumeAudioOnGesture();
        document.removeEventListener('click', startAudio);
        document.removeEventListener('touchstart', startAudio);
        document.removeEventListener('keydown', startAudio);
      };
      document.addEventListener('click', startAudio);
      document.addEventListener('touchstart', startAudio);
      document.addEventListener('keydown', startAudio);
      requestAnimationFrame(frame);
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

  /* ===== 测试接口 ===== */
  window.__game = {
    newGame: newGame,
    hardDrop: hardDrop,
    moveLeft: function () { moveH(-1); },
    moveRight: function () { moveH(1); },
    dropIntoColumn: dropIntoColumn,
    _setSpeed: function (s) { SPEED = s; },
    _load: function (state) { return loadState(state); },
    get board() {
      // 返回数值棋盘，便于测试断言
      return board.map(function (row) { return row.map(function (t) { return t ? t.v : 0; }); });
    },
    get score() { return score; },
    get best() { return best; },
    get moves() { return moves; },
    get merges() { return merges; },
    get maxTile() { return maxTile; },
    get currentTile() { return curTile ? curTile.v : cur; },
    get nextTile() { return next; },
    get fr() { return fr; },
    get fc() { return fc; },
    get phase() { return phase; },
    get gameOver() { return phase === 'over'; }
  };
})();