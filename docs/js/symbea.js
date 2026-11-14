(() => {
  const $ = id => document.getElementById(id);
  // 1 ページで 3 × 3（index.html）・1 輪（single.html）・花畑（garden.html）を切り替える。<body data-grid="3|1|garden">
  // 花畑は 3 × 3 と同じ 9 つの花（探索の単位）を、大・中・小の大きさで画面いっぱいに並べる
  const GARDEN = document.body.dataset.grid === "garden";
  const G = GARDEN ? 3 : +document.body.dataset.grid || 3, N = G * G;
  const store = {
    get(k) { try { return JSON.parse(localStorage.getItem(k)); } catch { return null; } },
    set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch {} },
  };
  // シード付き乱数。シードは 12 桁の整数 0 ≤ s < 10^12（日付 YYYYMMDDHHmm もそのまま使える）
  // s を上位・下位の 32bit に分け、系列番号 k と混ぜて 128bit 状態の sfc32 を初期化する。
  // 花 i は系列 i、色は系列 9。系列ごとに独立なので、探索の順番に結果が左右されない
  const SEED_SPACE = 1e12;
  const pad12 = s => String(s).padStart(12, "0");
  function splitmix32(a) {
    return () => {
      a = a + 0x9E3779B9 | 0;
      let z = a;
      z = Math.imul(z ^ z >>> 16, 0x85EBCA6B); z = Math.imul(z ^ z >>> 13, 0xC2B2AE35);
      return (z ^ z >>> 16) >>> 0;
    };
  }
  // (hi, lo, k) → 4 ワード。k を固定すると (hi, lo) に対して単射（各 splitmix32 の初回出力が種に対して全単射のため）
  function subSeed(hi, lo, k) {
    const a = splitmix32(lo), b = splitmix32(Math.imul(hi, 0x9E3779B1) ^ 0x6A09E667),
          c = splitmix32(Math.imul(k + 1, 0x85EBCA77) ^ 0xBB67AE85);
    const a0 = a(), b0 = b(), c0 = c();
    return [a0 ^ c0, b0 ^ a(), c0 ^ b(), a() ^ b() ^ c()].map(x => x >>> 0);
  }
  function sfc32(a, b, c, d) {
    const next = () => {
      const t = (a + b | 0) + d | 0;
      d = d + 1 | 0; a = b ^ b >>> 9; b = c + (c << 3) | 0; c = (c << 21 | c >>> 11) + t | 0;
      return (t >>> 0) / 4294967296;
    };
    for (let i = 0; i < 12; i++) next();       // 初期状態の偏りを捨てる
    return next;
  }
  const seedRng = (s, k) => sfc32(...subSeed(Math.floor(s / 4294967296), s % 4294967296, k));
  // 64bit を棄却サンプリングして 0〜10^12−1 の一様乱数にする
  function newSeed() {
    const N = 1000000000000n, LIMIT = (1n << 64n) - (1n << 64n) % N, w = new Uint32Array(2);
    for (;;) {
      crypto.getRandomValues(w);
      const v = BigInt(w[0]) << 32n | BigInt(w[1]);
      if (v < LIMIT) return Number(v % N);
    }
  }
  const freshRng = () => seedRng(newSeed(), 0);   // 再抽選・変奏・色の抽選など、シードに紐づかない乱数
  // 1〜12 桁の数字はそのまま、13 桁以上はエラー、それ以外の文字列は 64bit FNV-1a で 10^12 に収める
  function parseSeed(str) {
    str = String(str ?? "").trim();
    if (!str) return null;
    if (/^\d+$/.test(str)) {
      if (str.length > 12) throw new RangeError("シードは 12 桁まで（000000000000〜999999999999）です");
      return Number(str);
    }
    let h = 0xCBF29CE484222325n;
    for (const b of new TextEncoder().encode(str)) h = (h ^ BigInt(b)) * 0x100000001B3n & 0xFFFFFFFFFFFFFFFFn;
    return Number(h % 1000000000000n);
  }
  const dateSeed = d => Number(`${d.getFullYear()}${[d.getMonth() + 1, d.getDate(), d.getHours(), d.getMinutes()]
    .map(v => String(v).padStart(2, "0")).join("")}`);
  const rnd = (rng, lo, hi) => lo + rng() * (hi - lo);
  const pick = (rng, a) => a[Math.floor(rng() * a.length)];
  const clip = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
  const yieldUI = () => new Promise(r => setTimeout(r, 0));

  // ==================================================================================
  // 写像（ver.1 と同じ）
  // ==================================================================================
  let NX = 0, NY = 0;
  function step(q, x, y) {
    const zz = x * x + y * y;
    let zr = x, zi = y;                         // z^(n-1)
    for (let i = 1; i < q.n - 1; i++) { const t = zr * x - zi * y; zi = zr * y + zi * x; zr = t; }
    const ren = zr * x - zi * y;                // Re(z^n)
    const p = q.lam + q.alpha * zz + q.beta * ren;
    NX = p * x - q.omega * y + q.gamma * zr;
    NY = p * y + q.omega * x - q.gamma * zi;
  }

  // 過渡を捨てて境界半径を推定。発散・固定点なら null
  function probe(q, N = 20000) {
    let x = 0.01, y = 0.003, R = 0;
    for (let i = 0; i < N; i++) {
      step(q, x, y); x = NX; y = NY;
      if (!(Math.abs(x) + Math.abs(y) < 1e4)) return null;
      if (i > 1000) { const r = x * x + y * y; if (r > R) R = r; }
    }
    R = Math.sqrt(R);
    return R > 1e-6 ? { R, x, y } : null;
  }

  // 軌道を 128×128 に落としてボックス次元・余白・Lyapunov を測る
  function analyze(q) {
    const pr = probe(q);
    if (!pr) return null;
    const G = 128, h = new Uint8Array(G * G);
    let x = pr.x, y = pr.y;
    for (let i = 0; i < 80000; i++) {
      step(q, x, y); x = NX; y = NY;
      const gx = ((x / pr.R) * 0.5 + 0.5) * (G - 1) | 0, gy = ((y / pr.R) * 0.5 + 0.5) * (G - 1) | 0;
      if (gx >= 0 && gx < G && gy >= 0 && gy < G) h[gy * G + gx] = 1;
    }
    const occ32 = new Uint8Array(32 * 32), c = (G - 1) / 2;
    let c128 = 0, c32 = 0, occDisk = 0, disk = 0;
    for (let j = 0; j < G; j++) for (let i = 0; i < G; i++) {
      const dx = i - c, dy = j - c, inD = dx * dx + dy * dy <= (G / 2) ** 2;
      if (inD) disk++;
      if (!h[j * G + i]) continue;
      c128++; if (inD) occDisk++;
      const o = (j >> 2) * 32 + (i >> 2); if (!occ32[o]) { occ32[o] = 1; c32++; }
    }
    const d0 = 1e-8; let x2 = x + d0, y2 = y, lsum = 0;
    for (let i = 0; i < 3000; i++) {
      step(q, x, y); const ax = NX, ay = NY;
      step(q, x2, y2);
      const dx = NX - ax, dy = NY - ay, dd = Math.hypot(dx, dy) || 1e-300;
      lsum += Math.log(dd / d0);
      x = ax; y = ay; x2 = ax + dx * d0 / dd; y2 = ay + dy * d0 / dd;
    }
    return { D: Math.log2(c128 / Math.max(c32, 1)) / 2, fill: occDisk / disk, lyap: lsum / 3000 };
  }
  const isGood = a => a && a.D > 1.45 && a.D < 1.9 && a.fill > 0.15 && a.fill < 0.7 && a.lyap > 0.01;

  // ==================================================================================
  // 9 つの花のコンセプト
  // 写像は変えず、(1) 対称数 n と探索条件（余白の範囲）、(2) 同じ軌道を重ねる「層」で花らしさを与える。
  // 層 = { s: 半径, rot: 回転, dx, dy: 中心のずれ, warp: 極座標の変形 r → r^warp, dens: 面積あたりの点の濃さ,
  //        sy: 縦の縮率, upper: 回転後の上半分だけ描く,
  //        eq: 半径の均等化 r → √CDF(r)（軌道が中心から外周まで面積あたり均等に広がる。角度方向の形はそのまま）,
  //        mod: 姿の変化（花びらの輪郭・ねじれ）をかける }
  // どの層も、アトラクタの中心の穴（内径 r0）を r → (r − r0)/(1 − r0) で閉じ、花びらが中心から出るようにする
  // ==================================================================================
  const TAU = Math.PI * 2;
  const BALL = 0.55;                          // r → r^0.55：内側を押し広げて、球・円盤のように詰まった形にする
  // パラメータから決まる乱数（雄しべの配置など）。パラメータが同じなら同じ形になる。salt で系列を分ける
  function hashRng(q, salt = 0) {
    let h = 0x811C9DC5 ^ Math.imul(salt, 0x9E3779B9);
    for (const ch of [q.n, q.lam, q.alpha, q.beta, q.gamma, q.omega].map(v => (+v).toFixed(6)).join(","))
      h = Math.imul(h ^ ch.charCodeAt(0), 0x01000193);
    return sfc32(h >>> 0, 0x9E3779B9, 0x243F6A88, 0xB7E15162);
  }
  // 姿の変化：パラメータから決まる乱数で、花の大きさ・花びらの輪郭・ねじれ・層の構成を変える。
  // 輪郭は r → r·(1 − a(1 − |cos(k(θ − φ)/2)|^p))（k = n または 2n 枚の花びら、a: 切れ込みの深さ、p: 尖り）、
  // ねじれは θ → θ + tw·r。vary（パネルの「変化」）が 0 なら既定の姿、1 で花ごとの範囲いっぱいに変わる
  // salt：花畑で同じパラメータの花を並べるとき、1 輪ずつ姿を変える（0 なら 3 × 3・1 輪と同じ姿）
  function form(q, c, vary, salt = 0) {
    const r = hashRng(q, salt ? 1000 + salt * 2 : 1), F = c.form || {}, k = q.n * pick(r, F.m || [1]);
    const size = rnd(r, ...(F.size || [1, 1])), a = rnd(r, ...(F.a || [0, 0])), p = rnd(r, ...(F.p || [1, 1]));
    const phase = r() < 0.5 ? 0 : Math.PI / k, tw = (F.tw || 0) * rnd(r, -1, 1), lr = hashRng(q, salt ? 1001 + salt * 2 : 2);
    return {
      k, p, phase, size: 1 - (1 - size) * vary, a: Math.min(0.9, a * vary), tw: tw * vary,
      r: lr,
      v: (def, lo, hi) => def + (rnd(lr, lo, hi) - def) * Math.min(1, vary),   // 既定値から範囲内の値へ vary の割合で寄せる
      flag: (def, prob) => { const u = lr(); return vary > 0 ? u < prob : def; },
    };
  }
  // アマリリス：花の中心から伸びる 6 本の雄しべと 1 本の雌しべ。花糸はごく小さな軌道を点線のように並べ、先に葯（柱頭は 3 裂）を付ける
  function pistils(q, V) {
    const r = hashRng(q), out = [], L0 = V.v(0.55, 0.42, 0.7), bend = V.v(0, -0.12, 0.12);
    const line = (ang, len, tip) => {
      const D = 14;
      for (let j = 1; j <= D; j++) {
        const t = j / D, d = 0.1 + (len - 0.1) * t, a = ang + bend * t * t;
        out.push({ s: 0.012, rot: r() * TAU, dx: d * Math.cos(a), dy: d * Math.sin(a), dens: 8 });
      }
      const a = ang + bend;
      tip.forEach(([da, s]) => out.push({ s, rot: r() * TAU, dx: len * Math.cos(a + da), dy: len * Math.sin(a + da), dens: 12 }));
    };
    const base = r() * TAU;
    for (let i = 0; i < 6; i++) line(base + i * TAU / 6 + (r() - 0.5) * 0.25, L0 * (0.85 + r() * 0.2), [[0, 0.03 + r() * 0.01]]);
    line(base + TAU / 12, L0 * 1.12, [[-0.06, 0.022], [0, 0.022], [0.06, 0.022]]);     // 雌しべ（柱頭は 3 裂）
    return out;
  }
  // モモ：中心から長く伸びる雄しべの先の葯（やく）。同じ軌道をごく小さくして、半径をばらつかせた輪に並べる
  function stamens(q, V) {
    const r = hashRng(q), K = Math.round(V.v(24, 16, 36)), R0 = V.v(0.34, 0.24, 0.44), sp = V.v(0.08, 0.03, 0.14);
    return Array.from({ length: K }, (_, i) => {
      const a = (i + 0.5 * r()) * TAU / K, d = R0 + (r() * 2 - 1) * sp;
      return { s: 0.032 + r() * 0.016, rot: r() * TAU, dx: d * Math.cos(a), dy: d * Math.sin(a), dens: 6 };
    });
  }
  const disc = (s, dens = 3) => ({ s, warp: BALL, dens });     // 花の中心（同じ軌道を小さく丸めたもの）
  // form: 姿の変化の範囲（size: 大きさ、m: 花びらの数は n の何倍か、a: 切れ込みの深さ、p: 尖り、tw: ねじれの最大）
  const CONCEPTS = [
    { name: "ポインセチア", ns: [5, 6], omega0: true, fill: [0.15, 0.6],
      form: { size: [0.78, 1], m: [1], a: [0.15, 0.55], p: [1.5, 4], tw: 0.12 },
      layers: (q, V) => { const t = Math.round(V.v(2, 2, 3.4)), s2 = V.v(0.6, 0.45, 0.75);
        return [...Array.from({ length: t }, (_, k) => ({ s: s2 ** k, rot: k * Math.PI / q.n, mod: true })), disc(V.v(0.13, 0.08, 0.18), 2.5)]; } },
    { name: "マーガレット", ns: [9, 10, 11, 12], fill: [0.15, 0.5],
      form: { size: [0.78, 1], m: [2], a: [0.05, 0.4], p: [0.8, 2.5], tw: 0.15 },
      layers: (q, V) => [{ s: 1, mod: true }, ...(V.flag(true, 0.65) ? [{ s: V.v(0.96, 0.8, 1), rot: Math.PI / q.n, mod: true }] : []),
                         disc(V.v(0.22, 0.14, 0.32))] },
    // アマリリス：3 回対称の軌道で尖った花びら 3 枚の層を 2 つ、π/3 ずらして重ね、外花被 3 枚・内花被 3 枚の 6 弁の星形にする。
    // 中心は濃い喉、そこから雄しべ 6 本と雌しべ 1 本が伸びる
    { name: "アマリリス", ns: [3], omega0: true, fill: [0.25, 0.65], align: true,
      form: { size: [0.85, 1], m: [1], a: [0.35, 0.65], p: [1.5, 4], tw: 0.08 },
      layers: (q, V) => [{ s: 1, mod: true }, { s: V.v(0.88, 0.75, 0.95), rot: Math.PI / 3, mod: true },
                         disc(V.v(0.2, 0.14, 0.28), 3), ...pistils(q, V)] },
    { name: "アネモネ", ns: [5, 6, 7, 8], fill: [0.35, 0.7],
      form: { size: [0.75, 1], m: [1], a: [0.1, 0.45], p: [0.5, 1.6], tw: 0.25 },
      layers: (q, V) => [{ s: 1, mod: true }, ...(V.flag(false, 0.45) ? [{ s: V.v(0.65, 0.5, 0.78), rot: Math.PI / q.n, mod: true, dens: 0.8 }] : []),
                         disc(V.v(0.28, 0.18, 0.38), 4)] },
    { name: "センニチコウ", ns: [8, 9, 10, 11, 12], fill: [0.3, 0.7],
      form: { size: [0.6, 0.92], m: [2], a: [0.03, 0.2], p: [1, 3], tw: 0.25 },
      layers: (q, V) => { const t = Math.round(V.v(5, 3, 6.4));
        return Array.from({ length: t }, (_, k) => ({ s: 0.84 - k * 0.64 / (t - 1), rot: k * Math.PI / q.n + k * 0.11, warp: BALL, mod: true })); } },
    { name: "ダリア", ns: [8, 9, 10, 11, 12], fill: [0.2, 0.65],
      form: { size: [0.82, 1], m: [1], a: [0.15, 0.5], p: [0.8, 3], tw: 0.5 },
      layers: (q, V) => { const t = Math.round(V.v(6, 4, 8.4)), ratio = V.v(0.8, 0.72, 0.86), jit = V.v(0.06, 0, 0.18);
        return Array.from({ length: t }, (_, k) => ({ s: 0.98 * ratio ** k, rot: (k % 2) * Math.PI / q.n + k * jit, mod: true })); } },
    { name: "ニゲラ", ns: [5], fill: [0.12, 0.42],
      form: { size: [0.78, 1], m: [1, 2], a: [0.1, 0.4], p: [1, 3], tw: 0.2 },
      layers: (q, V) => [{ s: 1, rot: Math.PI / 5, dens: V.v(0.3, 0.12, 0.55) }, { s: V.v(0.7, 0.55, 0.82), mod: true }, disc(V.v(0.17, 0.1, 0.24))] },
    // モモ：丸く幅の広い 5 枚の花びら（4 割ほどは八重咲きで内側にもう 1 段）と、放射状に広がる雄しべの葯
    { name: "モモ", ns: [5], omega0: true, fill: [0.3, 0.7],
      form: { size: [0.8, 1], m: [1], a: [0.2, 0.5], p: [0.4, 1.2], tw: 0.05 },
      layers: (q, V) => [{ s: 1, mod: true }, ...(V.flag(false, 0.4) ? [{ s: V.v(0.68, 0.55, 0.8), rot: Math.PI / 5, mod: true }] : []),
                         ...stamens(q, V), disc(V.v(0.1, 0.07, 0.14), 3)] },
    // マリーゴールド：縮れた花びらが幾重にも重なるポンポン咲き。半径を均等化（eq）して中心まで花びらで埋め、
    // 回転をばらばらにずらした層を内側ほど詰めて重ねる
    { name: "マリーゴールド", ns: [9, 10, 11, 12], fill: [0.18, 0.5],
      form: { size: [0.72, 1], m: [2], a: [0.05, 0.28], p: [1, 3], tw: 0.5 },
      layers: (q, V) => { const t = Math.round(V.v(6, 4, 7.4)), ratio = V.v(0.8, 0.74, 0.86);
        return Array.from({ length: t }, (_, k) => ({ s: 0.97 * ratio ** k, rot: V.r() * TAU, eq: true, warp: k % 2 ? 0.85 : 1, dens: 1 + k * 0.15, mod: true })); } },
  ];

  // 確認済みのパラメータ（花ごとに 10 組）[n, λ, α, β, γ, ω]。ver.2 の基準・対称性・花の余白の範囲をすべて満たす。
  // 探索で 4000 回試しても見つからないときだけ、ここから選ぶ（めったに起きない）
  const LIB = [
    [[6,-2.68317,3.963443,-0.39696,-1.123296,0], [5,2.733986,-3.146568,-0.478931,-0.789091,0], [6,-1.628503,1.210729,0.812148,-1.167864,0], [6,-2.614832,3.280118,-0.701925,-0.5425,0], [5,-1.939089,2.364574,1.4156,-1.137584,0], [5,-2.324017,2.051365,-1.192669,0.841436,0], [5,2.035876,-2.282334,0.147206,-1.127017,0], [5,-2.219875,1.372859,0.592975,-0.494679,0], [6,2.511806,-3.734029,-0.707922,-1.034008,0], [5,2.709602,-3.778188,1.055306,0.549977,0]],
    [[10,2.303556,-4.41819,-1.245662,-0.779577,0.081783], [11,-2.320488,3.719851,0.890244,0.779235,0.276561], [9,-2.336197,2.501003,0.701183,-0.364954,-0.284364], [11,-2.305849,3.966476,-1.413192,-0.52242,-0.21184], [12,2.128203,-1.666402,0.950158,-0.695159,-0.026722], [10,-1.75757,1.099459,-0.949188,1.05982,0.115602], [12,-2.294955,3.904085,-1.198465,-1.055202,-0.162847], [11,2.208072,-2.877822,0.531518,1.191174,-0.124337], [11,-2.277593,3.720784,-0.92922,-0.333112,0.106754], [10,-2.277683,3.56774,-0.263301,-0.537398,-0.029412]],
    [[3,-1.623767,1.052026,0.616426,1.078095,0], [3,-1.812804,3.75919,0.22944,0.908587,0], [3,-1.842043,0.302364,-0.011551,0.283819,0], [3,-1.21174,-0.913403,-0.767145,-0.887182,0], [3,2.03498,-3.292828,-0.431193,-1.150373,0], [3,-1.709336,2.236277,-1.159831,-0.777255,0], [3,-2.068828,3.268301,-0.201175,0.724811,0], [3,1.669976,-1.014655,0.04364,0.724375,0], [3,2.156419,-3.463988,1.421627,0.938476,0], [3,2.765889,-4.791523,1.424949,0.240651,0]],
    [[5,2.300268,-1.704614,-0.016505,-0.529866,-0.257315], [5,-1.771995,1.467589,-1.451297,-0.086712,0.128172], [5,-2.119187,4.026247,0.653185,0.51342,-0.189487], [5,1.971841,-2.048087,0.322592,-1.106265,0.159305], [8,-2.304503,2.445654,-0.940122,0.443517,-0.272577], [7,2.37368,-2.829701,1.027825,-0.278435,-0.209299], [5,2.296282,-4.815512,-1.354131,-0.11713,0.146251], [7,-2.129014,1.890068,-1.087547,1.075203,0.161711], [8,2.214298,-2.469244,0.931928,-1.02004,0.252475], [5,-2.037134,4.017196,0.565044,1.121558,-0.262693]],
    [[11,1.991412,-1.627151,-0.418944,-0.450025,0.163384], [11,2.345572,-4.171975,0.194156,-0.297579,0.139734], [11,1.762519,-1.286588,-1.005233,-0.796956,0.233561], [9,-2.289758,4.434422,-1.360232,-1.060926,-0.029002], [8,2.256537,-2.308539,-0.954548,0.141516,-0.109819], [12,-2.417305,2.687364,1.170752,-0.13322,0.049582], [12,-1.393404,0.633654,-1.263984,-1.004344,0.21805], [8,-2.191793,1.91003,0.963451,-0.774249,-0.281064], [9,2.369316,-2.291878,0.424746,-0.106001,-0.267656], [9,-1.931221,1.363178,-0.464357,0.82238,-0.118042]],
    [[11,2.152617,-2.215659,-0.061735,-0.630269,0.297511], [8,2.21673,-1.658262,0.158777,-0.229107,0.261461], [11,-1.927987,1.629362,0.444569,-1.013384,-0.166641], [9,1.789718,-1.257541,0.557398,-0.95157,0], [8,2.214586,-1.44322,0.254734,-0.255912,0.166467], [11,-2.33284,3.454416,-0.56556,-0.203098,-0.257373], [11,-1.812837,1.286563,-0.535866,-0.601029,-0.014664], [10,-2.326463,4.547719,1.283469,0.461223,-0.086704], [11,2.314902,-4.854484,-1.24861,-0.502958,-0.052261], [9,1.93534,-1.200619,-0.453294,0.419653,0.258274]],
    [[5,-1.095844,-0.076298,-0.893813,-0.359306,0.105594], [5,-1.868415,0.243712,0.013585,-0.071469,0], [5,2.234204,-4.357495,0.54018,-0.878701,0.190934], [5,2.084878,-2.034307,-0.834134,0.520328,0.284835], [5,-1.413073,0.400002,0.052848,-0.580198,-0.082984], [5,2.161173,-3.691478,-1.461561,-0.695822,0.290738], [5,-1.273345,0.299994,-0.356426,-1.098707,-0.040017], [5,-1.003772,-0.612482,-1.494111,-1.171898,0.04581], [5,-2.0701,2.771876,0.112024,-0.441639,-0.057788], [5,-1.485856,0.875097,0.765451,0.705936,-0.244893]],
    [[5,2.543089,-4.108833,0.794296,0.894528,0], [5,-2.403787,2.967078,-0.7175,0.307318,0], [5,-2.082234,1.527086,-0.492313,0.687856,0], [5,-2.083816,2.343292,-0.866006,0.951509,0], [5,-2.360232,2.753722,0.493863,-0.147718,0], [5,2.733131,-4.482613,-0.957727,-0.936238,0], [5,-2.3585,3.479316,0.964975,-0.361943,0], [5,-2.121543,3.677114,-1.404214,1.139113,0], [5,2.012647,-2.200712,0.020153,-1.045602,0], [5,2.608605,-4.329654,-1.376755,-0.760824,0]],
    [[10,-2.121074,1.687003,0.469714,0.130355,-0.163301], [12,-2.33084,4.264915,0.399065,0.787289,-0.247889], [12,-2.381677,3.966986,-0.133012,0.190769,0.221612], [9,2.344565,-3.800539,-1.447674,0.700296,0.245972], [12,-2.306401,3.305019,-0.267913,-0.081371,0.162175], [9,-2.291144,3.525484,0.74213,0.240269,0.267593], [10,1.967261,-1.729137,-1.267791,1.117766,-0.285467], [11,-1.633868,0.802337,-0.152965,0.437361,0.088313], [11,2.314028,-4.702928,0.842258,0.064956,0.114077], [12,2.263266,-2.132136,-0.159285,-0.108595,-0.026622]],
  ];
  CONCEPTS.forEach((c, i) => { c.lib = LIB[i].map(([n, lam, alpha, beta, gamma, omega]) => ({ n, lam, alpha, beta, gamma, omega })); });

  // 乱数の使い方は ver.2 と同じ（n の抽選も 1 回の乱数）。n と ω だけ花ごとの範囲に収める
  function randomParams(rng, c) {
    const q = { n: pick(rng, c.ns), lam: rnd(rng, -2.8, 2.8), alpha: rnd(rng, -5, 5), beta: rnd(rng, -1.5, 1.5),
                gamma: rnd(rng, -1.2, 1.2), omega: rng() < 0.5 ? 0 : rnd(rng, -0.3, 0.3) };
    if (c.omega0) q.omega = 0;
    return q;
  }
  // 近傍のパラメータ（変奏）。対称数は 7 割で保ち、変えるときも花の範囲の中で
  function mutate(rng, q, s, c) {
    const r = v => +v.toFixed(3), others = c.ns.filter(v => v !== q.n);
    return {
      n: rng() < 0.7 || !others.length ? q.n : pick(rng, others),
      lam: r(clip(q.lam + rnd(rng, -0.15, 0.15) * s, -3, 3)), alpha: r(clip(q.alpha + rnd(rng, -0.4, 0.4) * s, -6, 6)),
      beta: r(clip(q.beta + rnd(rng, -0.15, 0.15) * s, -2, 2)), gamma: r(clip(q.gamma + rnd(rng, -0.12, 0.12) * s, -1.5, 1.5)),
      omega: c.omega0 || (q.omega === 0 && rng() < 0.7) ? 0 : r(clip(q.omega + rnd(rng, -0.05, 0.05) * s, -0.5, 0.5)),
    };
  }

  // 対称性が崩れたアトラクタを除く。n 回対称なら角度の Fourier 係数 E[e^{ijθ}] は j が n の倍数以外で 0 になるので、
  // j = 1 … n−1 の大きさがすべて 0.1 未満であることを確かめる（片側に寄った形や、2 回対称の蝶ネクタイ形を除く）
  function symmetric(q) {
    const pr = probe(q, 3000);
    if (!pr) return false;
    const N = 6000, re = new Float64Array(q.n), im = new Float64Array(q.n);
    let x = pr.x, y = pr.y;
    for (let i = 0; i < N; i++) {
      step(q, x, y); x = NX; y = NY;
      const r = Math.hypot(x, y); if (!r) continue;
      const wr = x / r, wi = y / r;
      let pr_ = 1, pi = 0;
      for (let j = 1; j < q.n; j++) { const t = pr_ * wr - pi * wi; pi = pr_ * wi + pi * wr; pr_ = t; re[j] += pr_; im[j] += pi; }
    }
    for (let j = 1; j < q.n; j++) if (Math.hypot(re[j], im[j]) / N >= 0.1) return false;
    return true;
  }
  // ver.2 の基準（isGood）を満たし、n 回対称が保たれ、さらに花ごとの余白の範囲に入る候補を探す。
  // 600 回までに花の余白の範囲に入る候補がなければ、ver.2 の基準と対称性だけを満たした最初の候補を使う。
  // 4000 回試してもどちらもなければ、確認済みのパラメータ（LIB）から最後の候補のハッシュで選ぶ。
  // どれも試す順番が決まっているので、同じシードなら同じ結果になり、「見つからない」ことはない
  async function search(gen, c, isStale, maxTries = 4000) {
    let fallback = null, q = null;
    for (let t = 0; t < maxTries; t++) {
      q = gen(); const a = analyze(q);
      if (isGood(a) && symmetric(q)) {
        if (a.fill >= c.fill[0] && a.fill <= c.fill[1]) return q;
        fallback ??= q;
      }
      if (fallback && t >= 600) return fallback;
      if (t % 6 === 5) { await yieldUI(); if (isStale()) return null; }
    }
    return fallback ?? { ...c.lib[Math.floor(hashRng(q)() * c.lib.length)] };
  }

  // ==================================================================================
  // 色彩：9 つ同色 / 9 つ別色。各花は 背景 → 花の色 → 深い色 のランプで塗る
  // 明るい背景では乗算、暗い背景ではスクリーンで重ねる
  // ==================================================================================
  const hex2rgb = h => [1, 3, 5].map(i => parseInt(h.slice(i, i + 2), 16));
  const rgb2hex = c => "#" + c.map(v => clip(Math.round(v), 0, 255).toString(16).padStart(2, "0")).join("");
  const hsl2hex = (h, s, l) => {
    const k = n => (n + h / 30) % 12, a = s * Math.min(l, 1 - l);
    return rgb2hex([0, 8, 4].map(n => 255 * (l - a * Math.max(-1, Math.min(k(n) - 3, 9 - k(n), 1)))));
  };
  function hex2hsl(hex) {
    const [r, g, b] = hex2rgb(hex).map(v => v / 255), mx = Math.max(r, g, b), mn = Math.min(r, g, b), l = (mx + mn) / 2, d = mx - mn;
    if (!d) return [0, 0, l];
    const s = d / (1 - Math.abs(2 * l - 1));
    const h = mx === r ? ((g - b) / d + 6) % 6 : mx === g ? (b - r) / d + 2 : (r - g) / d + 4;
    return [h * 60, s, l];
  }
  const lumOf = c => (0.299 * c[0] + 0.587 * c[1] + 0.114 * c[2]) / 255;
  const SKY = "#4fb0e3";
  const SKY9 = ["#4fb0e3", "#6cc4ec", "#3d97d6", "#58bcd9", "#7fb6ee", "#3a86c8", "#63c7e3", "#4b9fe6", "#8ccbef"];
  // deep / eachDeep：深い色（ランプの終わり）。null なら花の色と「芯の濃さ」から決める
  const COLOR_DEFAULT = { mode: "same", base: SKY, each: SKY9, bg: "#ffffff", transparent: false, depth: 0.55, gamma: 1.19, exposure: 1.5,
                          deep: null, eachDeep: Array(9).fill(null), set: "0" };
  // 色のセット：[名前, 背景, [花の色, 深い色] の組]。組が 1 つなら同色、複数なら花の種類ごとに順に割り当てる（別色）。
  // Flower Garden（https://symbealab.github.io/Generative-flower-Order-Chaos/garden.html）の色と同じ組み合わせ
  const COLOR_SETS = [
    ["スカイブルー（基本）", "#ffffff", [[SKY, null]]],
    ["紅と藍", "#f6efe8", [["#e0507f", "#1c1757"]]],
    ["夜光", "#05060b", [["#1f6bff", "#c8f6ff"]]],
    ["金糸", "#0c0907", [["#9c561a", "#ffe3a3"]]],
    ["夜桜", "#0b0509", [["#c2306e", "#ffd6ea"]]],
    ["翡翠の夜", "#03090a", [["#138a72", "#c9ffe9"]]],
    ["菫", "#07050f", [["#6b3cff", "#e6dcff"]]],
    ["炎", "#0a0503", [["#b8320c", "#ffd08a"]]],
    ["色とりどり（夜）", "#05060b", [["#1f6bff", "#c8f6ff"], ["#9c561a", "#ffe3a3"], ["#c2306e", "#ffd6ea"], ["#138a72", "#c9ffe9"], ["#6b3cff", "#e6dcff"]]],
    ["墨流し", "#f3eee4", [["#7a7f8a", "#111318"]]],
    ["藍染", "#eef2f3", [["#5b8fd0", "#0b1e4d"]]],
    ["翡翠", "#f1f4ef", [["#4fbf9a", "#073b30"]]],
    ["色とりどり（和紙）", "#f4efe6", [["#e0507f", "#1c1757"], ["#5b8fd0", "#0b1e4d"], ["#4fbf9a", "#073b30"], ["#d08a3a", "#3a1a05"], ["#7a7f8a", "#111318"]]],
  ];
  function applySet(i) {
    const [, bg, inks] = COLOR_SETS[i];
    Object.assign(color, { set: String(i), bg, transparent: false, depth: COLOR_DEFAULT.depth,
                           mode: inks.length > 1 && G !== 1 ? "each" : "same", base: inks[0][0], deep: inks[0][1] });
    if (i === 0) { color.each = [...SKY9]; color.eachDeep = Array(9).fill(null); }
    else { color.each = Array.from({ length: 9 }, (_, k) => inks[k % inks.length][0]); color.eachDeep = Array.from({ length: 9 }, (_, k) => inks[k % inks.length][1]); }
  }
  const COLOR_SLIDERS = [["depth", "芯の濃さ", 0, 0.9, 0.01, 2], ["gamma", "ガンマ", 0.3, 2, 0.01, 2],
                         ["exposure", "露出", 0.4, 3, 0.01, 2]];

  // 系統をそろえた 9 色（近い色相・補色・虹）と、同色用の 1 色
  function randomColor(rng) {
    const h0 = rng() * 360, scheme = pick(rng, ["analog", "analog", "split", "rainbow"]);
    const sat = () => rnd(rng, 0.5, 0.8), lit = () => rnd(rng, 0.48, 0.64);
    const base = hsl2hex(h0, sat(), lit());
    const step = rnd(rng, 5, 12);
    const each = Array.from({ length: 9 }, (_, i) => {
      const h = scheme === "analog" ? h0 + (i - 4) * step : scheme === "split" ? h0 + (i % 3) * 150 + rnd(rng, -10, 10) : h0 + i * 40;
      return hsl2hex((h % 360 + 360) % 360, sat(), lit());
    });
    return { base, each };
  }

  // 花の種類ごとのランプ（0〜1 の値。乗算用に 0 が背景側）。別色は花の種類に付く（並びが変わっても色は花についていく）
  const LUTS = Array.from({ length: 9 }, () => new Float32Array(256 * 3));
  const colorOf = i => color.mode === "each" ? color.each[i] : color.base;
  const deepOf = i => color.mode === "each" ? color.eachDeep[i] : color.deep;
  // 深い色の指定がなければ、花の色を「芯の濃さ」だけ暗く（暗い背景では明るく）する。
  // 指定があれば、花の色から深い色へ「芯の濃さ」の割合（既定 0.55 でちょうど深い色）で寄せる
  function endOf(hex, light, deep) {
    const [h, s, l] = hex2hsl(hex), mid = hex2rgb(hex).map(v => v / 255);
    if (deep) { const d = hex2rgb(deep).map(v => v / 255), t = color.depth / COLOR_DEFAULT.depth;
                return mid.map((v, k) => clip(v + (d[k] - v) * t, 0, 1)); }
    return light ? hex2rgb(hsl2hex(h, Math.min(1, s * 1.05), l * (1 - color.depth))).map(v => v / 255)
                 : hex2rgb(hsl2hex(h, s * 0.6, l + (1 - l) * color.depth)).map(v => v / 255);
  }
  function ramp(hex, light, deep) {
    const mid = hex2rgb(hex).map(v => v / 255), end = endOf(hex, light, deep);
    const start = light ? [1, 1, 1] : [0, 0, 0], M = 0.45;
    return t => t < M ? start.map((v, k) => v + (mid[k] - v) * (t / M))
                      : mid.map((v, k) => v + (end[k] - v) * ((t - M) / (1 - M)));
  }
  // 透明な背景は白い背景と同じく乗算で塗り、最後に白からの差をアルファに変える
  const isLight = () => color.transparent || lumOf(hex2rgb(color.bg)) > 0.5;
  function buildLUT() {
    const light = isLight();
    for (let i = 0; i < 9; i++) {
      const f = ramp(colorOf(i), light, deepOf(i)), L = LUTS[i];
      for (let t = 0; t < 256; t++) { const c = f(t / 255); L[t * 3] = c[0]; L[t * 3 + 1] = c[1]; L[t * 3 + 2] = c[2]; }
    }
    const toCss = (L, t) => `rgb(${[0, 1, 2].map(k => Math.round(L[t * 3 + k] * 255)).join(",")})`;
    $("swatch").style.background = color.mode === "each"
      ? `linear-gradient(90deg, ${LUTS.map((L, i) => `${toCss(L, 150)} ${i * 100 / 9}% ${(i + 1) * 100 / 9}%`).join(",")})`
      : `linear-gradient(90deg, ${[0, 32, 64, 96, 128, 160, 192, 224, 255].map((t, i) => `${toCss(LUTS[0], t)} ${i * 12.5}%`).join(",")})`;
  }

  // ==================================================================================
  // 一枚のキャンバスに 9 つの花を描く
  // 花ごとにヒストグラムを持ち、合成時に花ごとに正規化 → 花ごとの色で塗って重ねる
  // ==================================================================================
  const SKEY = GARDEN ? "symbea.flower.garden.v1" : G === 1 ? "symbea.flower.single.v1" : "symbea.flower.v3";   // v2 以前は花の種類・姿の変化が違うので読まない
  const saved = store.get(SKEY) || {};
  const color = { ...COLOR_DEFAULT, ...(saved.color || {}) };
  if (!Array.isArray(color.each) || color.each.length !== 9) color.each = [...SKY9];
  if (!Array.isArray(color.eachDeep) || color.eachDeep.length !== 9) color.eachDeep = Array(9).fill(null);
  if (saved.color && !("set" in saved.color)) color.set = "";     // セットがなかったころに保存した色はカスタム扱い
  if (color.set !== "" && !COLOR_SETS[+color.set]) color.set = "";
  if (G === 1) color.mode = "same";          // 1 輪では同色だけ
  const layout = { size: GARDEN ? 1 : 0.92, vary: 1, motion: "dynamic", ...(saved.layout || {}) };
  // 既定は動的。自分で「動き」を選んでいなければ（静的が既定だったころの保存も）動的にする
  if (!layout.motionChosen) layout.motion = "dynamic";
  let seed = Number.isSafeInteger(saved.seed) && saved.seed >= 0 && saved.seed < SEED_SPACE ? saved.seed : null, edited = !!saved.edited;

  // 点の数は花の面積に比例させる（1 輪は 3 × 3 の 1 マスより 9 倍大きいので、上限 6 倍まで増やす）
  // 花畑のキャンバスは壁紙と同じ大きさ（1320 × 2868 / 1440 × 3200）。S は幅、CH は高さ（3 × 3・1 輪は正方形で CH = S）
  const WP_SIZES = { iphone: { w: 1320, h: 2868, label: "iPhone" }, android: { w: 1440, h: 3200, label: "Android" } };
  const WKEY = "symbea.flower.wpsize";
  let wpSize = WP_SIZES[store.get(WKEY)] ? store.get(WKEY) : "iphone";
  const canvas = $("cv"), wrap = $("wrap"), ctx = canvas.getContext("2d");
  let S = canvas.width, CH = canvas.height, img = null, F = null;
  function sizeCanvas(w, h) {
    canvas.width = S = w; canvas.height = CH = h;
    img = ctx.createImageData(S, CH); F = new Float32Array(S * CH * 3);
    wrap.style.setProperty("--ar", `${w} / ${h}`); wrap.style.setProperty("--arw", `${w / h}`);
  }
  if (GARDEN) { wrap.classList.add("tall"); sizeCanvas(WP_SIZES[wpSize].w, WP_SIZES[wpSize].h); } else sizeCanvas(S, S);
  const CELL = S / G, TOTAL = 2.5e6 * Math.min(6, (CELL / 480) ** 2);
  const flowers = [];

  for (let i = 0; i < N; i++) {
    const mark = Object.assign(document.createElement("div"), { className: "mark" });
    mark.style.left = `${(i % G) * 100 / G}%`; mark.style.top = `${Math.floor(i / G) * 100 / G}%`;
    mark.style.width = mark.style.height = `${100 / G}%`;
    const busy = Object.assign(document.createElement("span"), { className: "busy", hidden: true });
    mark.append(busy);
    if (!GARDEN) $("marks").append(mark);    // 花畑では目印は 1 輪ずつ（relayout で作る）、探索中の表示はまとめて 1 つ
    flowers.push({ idx: i, ci: i, concept: CONCEPTS[i], q: null, job: 0, gen: 0, hist: null, C: 0, max: 1, pts: 0, mark, busy });
  }
  // マス f に花の種類 ci を割り当てる
  function setConcept(f, ci) {
    f.ci = ci; f.concept = CONCEPTS[ci];
  }

  // ==================================================================================
  // 花畑：大・中・小の円をランダムに、重なりを少しだけ許して画面いっぱいに詰める。
  // 配置・どの花を置くか・回転・姿の変化はシードの系列 12 で決まる（同じシードと大きさなら同じ花畑）。
  // 大きい順に並べ、先頭の 9 輪は 9 つの花（3 × 3 の並び順）そのもの、残りは 9 つの花からランダムに選び、
  // 回転と姿の変化（花びらの輪郭・ねじれ・層の構成）を 1 輪ずつ変える
  // ==================================================================================
  const GSIZES = { L: [0.44, 0.56], M: [0.27, 0.35], S: [0.13, 0.20] };   // 直径（基準の長さ m に対する比）
  const GMAX = 110;                                                      // 描く量が多くなりすぎないよう上限
  let pieces = [];
  // W × H px に並べる。花の大きさの基準は幅（正方形のビジュアルと縦長の壁紙で、幅に対する花の大きさが同じ）。
  // 面積が正方形の a 倍なら、隙間を埋める小・中の花の数と上限も a 倍にする（正方形では従来どおり）
  function gardenLayout(s, W = S, H = CH) {
    const r = seedRng(s, 12), m = W * 0.7 * layout.size, a = H / W, out = [];
    const R = (a, b) => a + r() * (b - a);
    const fits = (x, y, rad) => out.every(o => Math.hypot(o.x - x, o.y - y) >= (o.r + rad) * 0.86);
    const place = (cls, count, attempts) => {
      for (let c = 0; c < count; c++) {
        for (let t = 0; t < attempts; t++) {
          const rad = R(...GSIZES[cls]) * m / 2;
          // 端からは半径の 25% まではみ出してよい（画面の縁まで花で埋める）
          const x = R(rad * 0.75, W - rad * 0.75), y = R(rad * 0.75, H - rad * 0.75);
          if (fits(x, y, rad)) { out.push({ cls, x, y, r: rad }); break; }
        }
      }
    };
    const k = W * H / (m * m);
    place("L", Math.max(1, Math.round(k * (0.9 + r() * 0.5))), 300);
    place("M", Math.round(k * 4.5), 300);
    place("S", Math.round(120 * a), 300);
    place("M", Math.round(8 * a), 200); place("S", Math.round(60 * a), 200);      // 残った隙間にもう一度、中 → 小の順で
    out.sort((a, b) => b.r - a.r);
    return out.slice(0, Math.round(GMAX * a)).map((o, i) => ({
      ...o, fi: i < N ? i : Math.floor(r() * N), angle: r() * TAU, salt: i < N ? 0 : 1 + Math.floor(r() * 1e6),
      job: 0, hist: null, C: 0, max: 1, pts: 0, ox: 0, oy: 0, mark: null,
    }));
  }
  // 並べ直す（シード・大きさが変わったとき）。目印も作り直す
  function relayout() {
    pieces.forEach(p => { p.job++; p.hist = null; });
    gq.length = 0;
    pieces = gardenLayout(seed ?? 0);
    const marks = $("marks");
    marks.replaceChildren(gBusy.parentNode);
    for (const p of pieces) {
      p.mark = Object.assign(document.createElement("div"), { className: "mark" });
      Object.assign(p.mark.style, { left: `${(p.x - p.r) / S * 100}%`, top: `${(p.y - p.r) / CH * 100}%`,
                                    width: `${p.r * 2 / S * 100}%`, height: `${p.r * 2 / CH * 100}%`, borderRadius: "50%" });
      marks.append(p.mark);
    }
    requestPaint();
  }
  // 花畑の探索中の表示（9 つのうちいくつ探索中か）
  const gBusy = Object.assign(document.createElement("span"), { className: "busy", hidden: true });
  if (GARDEN) {
    const m = Object.assign(document.createElement("div"), { className: "mark" });
    Object.assign(m.style, { left: 0, top: 0, width: "100%", height: "100%" });
    m.append(gBusy); $("marks").append(m);
  }
  function updateBusy() {
    if (!GARDEN) return;
    const k = flowers.filter(f => !f.busy.hidden).length;
    gBusy.hidden = !k; gBusy.textContent = `探索中…（残り ${k} / ${N}）`;
  }
  // 花畑の描画待ち。一度にたくさん描くと重いので、大きい花から 4 輪ずつ
  const gq = [];
  let gActive = 0;
  function enqueuePiece(p) {
    p.job++; p.hist = null;                      // 描きかけの古い花は止める
    if (!gq.includes(p)) gq.push(p);
    gq.sort((a, b) => b.r - a.r);
    pumpPieces();
  }
  function pumpPieces() {
    while (gActive < 4 && gq.length) {
      const p = gq.shift(), f = flowers[p.fi];
      if (!pieces.includes(p) || !f.q) continue;
      gActive++;
      const C = pieceSize(p);
      draw(p, f.q, f.concept, C, p.x, p.y, p.angle, p.salt, pieceTotal(C), () => { gActive--; pumpPieces(); });
    }
  }
  // 花は円より少し小さく描かれるので、やや大きめにして隙間を埋める。点の数は面積に比例（3 × 3 と同じ密度）
  const pieceSize = p => Math.round(p.r * 2.2);
  // 花畑は壁紙の大きさで正方形の 2 倍ほどの面積を描くので、密度は 3 × 3 の半分（見た目はほぼ同じ）
  const pieceTotal = C => Math.max(2e5, 1.25e6 * (C / 442) ** 2);
  // 花 f（探索の単位）を描き直す。花畑では f を使っている花すべて
  function clearFlower(f) {
    f.job++; f.hist = null;
    if (GARDEN) pieces.forEach(p => { if (p.fi === f.idx) { p.job++; p.hist = null; } });
  }

  // 1 フレームに 1 回だけ合成する
  let paintReq = 0;
  const requestPaint = () => { if (!paintReq) paintReq = requestAnimationFrame(() => { paintReq = 0; paint(); }); };
  const drawables = () => GARDEN ? pieces.map(p => [p, flowers[p.fi]]) : flowers.map(f => [f, f]);
  function paint() {
    wrap.style.background = color.bg; wrap.classList.toggle("clear", color.transparent);
    $("seed").style.color = isLight() ? "rgba(0, 0, 0, .3)" : "rgba(255, 255, 255, .32)";
    if (motionOn()) return;                       // 動的なときは毎フレーム animate が描く
    compose(drawables(), S, CH, F, img.data);
    ctx.putImageData(img, 0, 0);
  }
  // 保存用の静止画（動的なときも、回転・点灯していない静的な姿を合成する）
  function stillCanvas() {
    if (!motionOn()) return canvas;
    compose(drawables(), S, CH, F, img.data);
    const out = Object.assign(document.createElement("canvas"), { width: S, height: CH });
    out.getContext("2d").putImageData(img, 0, 0);
    return out;
  }

  // ==================================================================================
  // 動的モーション：花ごとに 70〜90 bpm の心拍で、ゆっくり回りながら点灯する。
  // 花ごとのヒストグラムを色付きの画像（スプライト）にしておき、毎フレーム回転・拡大して重ねる
  // （明るい背景では乗算、暗い背景ではスクリーン。静的な合成と同じ重ね方）。
  // 心拍は「ドクン（強）・ドクン（弱）」の 2 つの山で、山のときに少し大きくなり、同じ花をもう一度薄く重ねて点灯させる。
  // テンポ・位相・回転の向きと速さは花ごとに、シードの系列 20 + 番号で決まる
  // ==================================================================================
  const motionOn = () => layout.motion === "dynamic";
  const bump = (x, c, w) => { const u = (x - c) / w; return Math.exp(-u * u); };
  const heart = ph => bump(ph, 0.02, 0.045) + 0.55 * bump(ph, 0.24, 0.05) + bump(ph, 1.02, 0.045);
  let colorVer = 0, animReq = 0, motionT0 = 0;      // motionT0：動き始めた時刻（そのときの向きは静的な姿と同じ）
  function motionOf(d, i) {
    if (!d.mo) {
      const r = seedRng(((seed ?? 0) + i * 7919) % SEED_SPACE, 20), small = GARDEN ? clip(1 - d.r / (S * 0.25), 0, 1) : 0;
      d.mo = { bpm: 70 + 20 * r(), ph: r(),
               spin: (r() < 0.5 ? -1 : 1) * (0.04 + 0.05 * r()) * (1 + 0.8 * small) };   // rad/s（およそ 2〜5°/s、小さい花ほど少し速い）
    }
    return d.mo;
  }
  // ヒストグラム → 色付きのスプライト（花の画素だけ不透明、ほかは透明）
  function sprite(d, f) {
    const key = `${d.job}|${colorVer}|${f.ci}`, now = performance.now();
    if (d.spr && d.sprKey === key && (d.sprPts === d.pts || now - d.sprAt < 400)) return d.spr;
    const C = d.C, h = d.hist, lm = Math.log1p(d.max), L = LUTS[f.ci], g = color.gamma, ex = color.exposure;
    if (!d.spr || d.spr.width !== C) d.spr = Object.assign(document.createElement("canvas"), { width: C, height: C });
    const c = d.spr.getContext("2d"), im = c.createImageData(C, C), px = im.data;
    for (let k = 0; k < C * C; k++) {
      const v0 = h[k]; if (!v0) continue;
      const t = (Math.min(1, Math.pow(Math.log1p(v0) / lm, g) * ex) * 255) | 0;
      px[k * 4] = L[t * 3] * 255; px[k * 4 + 1] = L[t * 3 + 1] * 255; px[k * 4 + 2] = L[t * 3 + 2] * 255; px[k * 4 + 3] = 255;
    }
    c.putImageData(im, 0, 0);
    d.sprKey = key; d.sprPts = d.pts; d.sprAt = now;
    return d.spr;
  }
  function animate(ms) {
    animReq = 0;
    if (!motionOn()) return;
    const t = ms / 1000, light = isLight(), op = light ? "multiply" : "screen";
    ctx.save();
    ctx.globalCompositeOperation = "source-over"; ctx.globalAlpha = 1;
    if (color.transparent) ctx.clearRect(0, 0, S, CH); else { ctx.fillStyle = color.bg; ctx.fillRect(0, 0, S, CH); }
    ctx.globalCompositeOperation = op;
    drawables().forEach(([d, f], i) => {
      if (!d.hist || !f.q) return;
      const mo = motionOf(d, i), spr = sprite(d, f);
      const env = heart(((t * mo.bpm / 60 + mo.ph) % 1 + 1) % 1);
      const C = d.C, cx = d.ox + C / 2, cy = d.oy + C / 2, sc = 1 + 0.045 * env;
      ctx.setTransform(1, 0, 0, 1, cx, cy); ctx.rotate(mo.spin * (t - motionT0)); ctx.scale(sc, sc);
      ctx.globalAlpha = 1; ctx.drawImage(spr, -C / 2, -C / 2);
      if (env > 0.03) { ctx.globalAlpha = Math.min(1, 0.55 * env); ctx.drawImage(spr, -C / 2, -C / 2); }   // 点灯
    });
    ctx.restore();
    animReq = requestAnimationFrame(animate);
  }
  function setMotion(m) {
    layout.motion = m; save();
    document.querySelectorAll('input[name="motion"]').forEach(r => { r.checked = r.value === m; });
    if (motionOn()) { motionT0 = performance.now() / 1000; if (!animReq) animReq = requestAnimationFrame(animate); }
    else { cancelAnimationFrame(animReq); animReq = 0; ctx.setTransform(1, 0, 0, 1, 0, 0); requestPaint(); }
  }
  // [ヒストグラムを持つもの, 花] の組を W × H px に合成して、RGBA の d に書く（F は作業用の W × H × 3）
  function compose(items, W, H, F, d) {
    const BG = hex2rgb(color.bg), light = isLight(), clear = color.transparent, g = color.gamma, ex = color.exposure;
    F.fill(light ? 1 : 0);
    for (const [it, f] of items) {
      if (!it.hist || !f.q) continue;
      const C = it.C, h = it.hist, lm = Math.log1p(it.max), L = LUTS[f.ci], ox = it.ox, oy = it.oy;
      for (let j = 0; j < C; j++) {
        const y = oy + j; if (y < 0 || y >= H) continue;
        for (let i = 0; i < C; i++) {
          const v0 = h[j * C + i]; if (!v0) continue;
          const x = ox + i; if (x < 0 || x >= W) continue;
          const t = (Math.min(1, Math.pow(Math.log1p(v0) / lm, g) * ex) * 255) | 0, k = (y * W + x) * 3;
          if (light) { F[k] *= L[t * 3]; F[k + 1] *= L[t * 3 + 1]; F[k + 2] *= L[t * 3 + 2]; }   // 乗算
          else for (let c = 0; c < 3; c++) F[k + c] = 1 - (1 - F[k + c]) * (1 - L[t * 3 + c]);   // スクリーン
        }
      }
    }
    for (let p = 0, k = 0; p < W * H; p++, k += 3) {
      if (clear) {   // 白に重ねたときに乗算の結果と同じ色になるアルファと色
        const al = 1 - Math.min(F[k], F[k + 1], F[k + 2]);
        for (let c = 0; c < 3; c++) d[p * 4 + c] = al > 0 ? 255 * (F[k + c] - 1 + al) / al : 0;
        d[p * 4 + 3] = 255 * al;
        continue;
      }
      for (let c = 0; c < 3; c++) d[p * 4 + c] = light ? BG[c] * F[k + c] : 255 - (255 - BG[c]) * (1 - F[k + c]);
      d[p * 4 + 3] = 255;
    }
  }

  // 描き終えた花の外形（左端と下端、キャンバスの px）。点のごく一部（0.1%）のはみ出しは無視する
  function flowerBox(f) {
    const C = f.C, h = f.hist, col = new Uint32Array(C), row = new Uint32Array(C);
    let tot = 0;
    for (let j = 0; j < C; j++) for (let i = 0; i < C; i++) if (h[j * C + i]) { col[i]++; row[j]++; tot++; }
    if (!tot) return null;
    const cut = tot * 0.001;
    let a = 0, left = 0, bottom = C - 1;
    for (; left < C - 1; left++) { a += col[left]; if (a > cut) break; }
    a = 0;
    for (; bottom > 0; bottom--) { a += row[bottom]; if (a > cut) break; }
    return { left: f.ox + left, bottom: f.oy + bottom };
  }
  // シードの位置（キャンバスの px、x は左端、y はベースライン）。
  // 3 × 3 はビジュアルの左下。1 輪は花が小さく真ん中にあるので、花の左下（左へ 0.035S、下へ 0.035S）に寄せる
  // 花畑は壁紙と同じく、安全領域の内側の左下
  function seedPos() {
    if (GARDEN) { const m = S * (1 - SAFE) / 2; return { x: m, y: CH - m }; }
    const f = flowers[0], dflt = { x: S * 0.012, y: S * 0.99 };
    if (G !== 1 || !f.box) return dflt;
    return { x: clip(f.box.left - S * 0.035, dflt.x, S * 0.5), y: clip(f.box.bottom + S * 0.035, S * 0.5, dflt.y) };
  }
  // 画面のシード表示も同じ位置に置く（画像と同じ見え方にする）
  function placeSeed() {
    const el = $("seed"), p = seedPos();
    if (G !== 1 && !GARDEN) return;
    el.style.left = `${p.x / S * 100}%`; el.style.top = `${p.y / CH * 100}%`; el.style.bottom = "auto";
    el.style.transform = "translateY(-80%)"; el.style.fontSize = `${S * 0.013 / S * 100}cqw`;
  }

  // 花 f を描く。3 × 3・1 輪はマスの中央に、花畑は f を使っている花すべてを描き直す
  function render(f) {
    if (GARDEN) { pieces.forEach(p => { if (p.fi === f.idx) enqueuePiece(p); }); return; }
    draw(f, f.q, f.concept, Math.round(CELL * layout.size), (f.idx % G + 0.5) * CELL, (Math.floor(f.idx / G) + 0.5) * CELL, 0, 0, TOTAL,
         done => { if (done && G === 1) { f.box = flowerBox(f); placeSeed(); } });
  }
  // d（ヒストグラムを持つもの）に、パラメータ q の花を、中心 (cx, cy)・一辺 C px・回転 angle・姿の変化 salt で描く。
  // 描き終えたら end(true)、途中で打ち切られたら end(false)
  function draw(d, q, concept, C, cx, cy, angle, salt, total, end) {
    const id = ++d.job;
    const run = plotter(d, q, concept, C, cx, cy, angle, salt);
    if (!run) { requestPaint(); end?.(false); return; }
    const CHUNK = 120000;
    (function chunk() {
      if (id !== d.job) { end?.(false); return; }
      run(CHUNK);
      requestPaint();
      if (d.pts < total) requestAnimationFrame(chunk);
      else end?.(true);
    })();
  }
  // d にヒストグラム（一辺 C px、左上 (ox, oy)）を用意し、点を count 個ずつ打つ関数 run(count) を返す。発散する花は null
  function plotter(d, q, concept, C, cx, cy, angle, salt) {
    d.C = C; d.ox = Math.round(cx - C / 2); d.oy = Math.round(cy - C / 2);
    d.hist = new Float32Array(C * C); d.max = 1; d.pts = 0; d.box = null;
    const pr = q && probe(q);
    if (!pr) { d.hist = null; return null; }
    const f = d, half = C / 2 - C / 90, inv = 1 / (pr.R * 1.02), h = d.hist;
    // 中心の穴の半径（内径）と、半径の累積分布（eq の層で使う）を短い軌道で測る
    // align の花は、花びらの輪郭をアトラクタの張り出す向きに合わせるため、Σ r²·e^{inθ} の偏角も測る
    let x = pr.x, y = pr.y, rmin = Infinity, ex = 0, ey = 0;
    const NB = 512, cdf = new Float32Array(NB + 1);
    for (let i = 0; i < 30000; i++) {
      step(q, x, y); x = NX; y = NY; const r = x * x + y * y; if (r < rmin) rmin = r;
      cdf[Math.min(NB - 1, Math.sqrt(r) * inv * NB | 0) + 1]++;
      if (concept.align && r > 0) {
        const th = Math.atan2(y, x) * q.n; ex += r * Math.cos(th); ey += r * Math.sin(th);
      }
    }
    for (let i = 1; i <= NB; i++) cdf[i] += cdf[i - 1];
    for (let i = 0; i <= NB; i++) cdf[i] = Math.sqrt(cdf[i] / cdf[NB]);
    const r0 = Math.min(0.9, Math.sqrt(rmin) * inv * 0.94), k0 = 1 / (1 - r0);
    x = pr.x; y = pr.y;
    const V = form(q, concept, layout.vary, salt), sz = V.size * half;
    if (concept.align) V.phase = Math.atan2(ey, ex) / q.n;
    const ca = Math.cos(angle), sa = Math.sin(angle);
    const L = concept.layers(q, V).map(l => {
      l = { s: 1, rot: 0, dx: 0, dy: 0, warp: 1, dens: 1, sy: 1, upper: false, eq: false, mod: false, ...l };
      if (angle) l = { ...l, rot: l.rot + angle, dx: l.dx * ca - l.dy * sa, dy: l.dx * sa + l.dy * ca };   // 花ごと回す
      return { ...l, cs: Math.cos(l.rot) * l.s * sz, sn: Math.sin(l.rot) * l.s * sz, mod: l.mod && (V.a > 0 || V.tw !== 0),
               ox: C / 2 + l.dx * sz, oy: C / 2 - l.dy * sz, w: l.s * l.s * l.dens };
    });
    // 軌道の点を層に配る。割合は 面積 × 濃さ に比例（4096 個の枠に並べる）。
    // 軌道は n 個の花びらを周期的に巡るので、点の番号を整数ハッシュで混ぜて枠を選ぶ（周期と同期すると層ごとに一部の花びらしか描かれない）
    const NS = 4096, slots = new Uint16Array(NS), wsum = L.reduce((a, l) => a + l.w, 0);
    let acc = 0, k = 0;
    L.forEach((l, j) => { acc += l.w / wsum * NS; while (k < Math.round(acc)) slots[k++] = j; });
    while (k < NS) slots[k++] = L.length - 1;
    let n = 0;
    return CHUNK => {
      for (let i = 0; i < CHUNK; i++, n++) {
        step(q, x, y); x = NX; y = NY;
        let hs = Math.imul(n ^ n >>> 16, 0x45D9F3B); hs = Math.imul(hs ^ hs >>> 16, 0x45D9F3B);
        const l = L[slots[(hs ^ hs >>> 16) >>> 20]];
        let u = x * inv, v = y * inv;
        const r = Math.hypot(u, v);
        if (r > 0) {
          let rr;
          if (l.eq) { const t = Math.min(NB, r * NB), i0 = Math.min(NB - 1, t | 0); rr = cdf[i0] + (cdf[i0 + 1] - cdf[i0]) * (t - i0); }
          else rr = Math.max(0, (r - r0) * k0);
          if (l.warp !== 1) rr = Math.pow(rr, l.warp);
          if (l.mod) {
            let th = Math.atan2(v, u);
            if (V.a) rr *= 1 - V.a * (1 - Math.pow(Math.abs(Math.cos(V.k * (th - V.phase) / 2)), V.p));
            th += V.tw * rr; u = rr * Math.cos(th); v = rr * Math.sin(th);
          } else { const m = rr / r; u *= m; v *= m; }
        }
        const ry = u * l.sn + v * l.cs;
        if (l.upper && ry < 0) continue;
        const px = (l.ox + u * l.cs - v * l.sn) | 0, py = (l.oy - ry * l.sy) | 0;
        if (px >= 0 && px < C && py >= 0 && py < C) { const c = ++h[py * C + px]; if (c > f.max) f.max = c; }
      }
      f.pts += CHUNK;
    };
  }

  // 条件を満たすパラメータを探して差し替える（gen を進めると古い探索は破棄される）
  async function roll(f, gen) {
    const my = ++f.gen;
    f.busy.textContent = "探索中…"; f.busy.hidden = false; updateBusy();
    const q = await search(gen, f.concept, () => my !== f.gen);
    if (my !== f.gen) return;
    if (!q) return;                               // search は必ず候補を返す（ここに来るのは打ち切られたときだけ）
    f.busy.hidden = true; updateBusy();
    f.q = q; render(f); save();
  }

  // 9 つを同時に探索すると重いので 3 並列で順番に（新しい一括探索が始まったら古いものは打ち切る）
  let batch = 0;
  async function rollMany(list, genFor) {
    const my = ++batch, gens = list.map(genFor);
    let next = 0;
    const worker = async () => { while (next < list.length && my === batch) { const i = next++; await roll(list[i], gens[i]); } };
    await Promise.all([worker(), worker(), worker()]);
  }

  // 並び順：系列 10 で 9 種の花をシャッフル（Fisher–Yates）
  function order(s) {
    const r = seedRng(s, 10), p = [...Array(9).keys()];
    for (let i = 8; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [p[i], p[j]] = [p[j], p[i]]; }
    return p;
  }
  // シードから生成。マス i の花は系列 i、色は系列 9、並び順は系列 10 を使う。
  // 1 輪のときは並び順の先頭の種類になるので、花の種類もシードでランダムに決まる（3 × 3 の左上と同じ花）
  function generate(s) {
    seed = s; edited = false;
    flowers.forEach(f => { f.mo = null; });        // 心拍のテンポ・回転もシードで決め直す
    const perm = order(seed);
    flowers.forEach(f => {
      if (f.ci !== perm[f.idx]) { clearFlower(f); f.q = null; }
      setConcept(f, perm[f.idx]);
    });
    if (GARDEN) relayout();
    requestPaint();
    if ($("rollColor").checked) randomize(seedRng(seed, 9));
    showSeed(); save();
    rollMany(flowers, f => { const rng = seedRng(seed, f.idx); return () => randomParams(rng, f.concept); });
  }
  function markEdited() {
    if (edited) return;
    edited = true; showSeed(); save();
  }
  function showSeed() {
    $("seed").textContent = seed === null ? "" : `seed ${pad12(seed)}${edited ? " *" : ""}`;
    $("seedIn").placeholder = seed === null ? "12 桁のシード" : pad12(seed);
    $("seedCur").textContent = seed === null ? "—" : `${pad12(seed)}${edited ? "（編集済み）" : ""}`;
    $("seedCopy").disabled = seed === null;
    try {
      const url = new URL(location.href);
      if (seed !== null && !edited) url.searchParams.set("seed", pad12(seed)); else url.searchParams.delete("seed");
      history.replaceState(null, "", url);
    } catch {}
  }

  function save() {
    store.set(SKEY, { cells: flowers.map(f => ({ ci: f.ci, q: f.q })), color, layout, sel: sel ? sel.idx : N >> 1, seed, edited });
  }

  // ==================================================================================
  // パネル
  // ==================================================================================
  function slider(parent, label, lo, hi, st, digits, get, set) {
    const lab = document.createElement("label"); lab.className = "sl";
    lab.innerHTML = `<span>${label}</span>`;
    const inp = Object.assign(document.createElement("input"), { type: "range", min: lo, max: hi, step: st });
    const out = document.createElement("output");
    const show = () => { inp.value = get(); out.textContent = (+get()).toFixed(digits); };
    inp.addEventListener("input", () => { set(+inp.value); out.textContent = (+inp.value).toFixed(digits); });
    lab.append(inp, out); parent.append(lab);
    return show;
  }

  let layoutTimer = null;
  slider($("layoutSliders"), "大きさ", 0.6, 1.5, 0.01, 2, () => layout.size, v => {
    layout.size = v;
    clearTimeout(layoutTimer);
    // 花畑は大きさで並べ方が変わるので並べ直す
    layoutTimer = setTimeout(() => { if (GARDEN) relayout(); flowers.forEach(f => f.q && render(f)); save(); }, GARDEN ? 250 : 80);
  })();
  // 姿の変化の強さ（0 で花ごとの既定の姿、1 で標準、1.5 まで強められる）
  slider($("layoutSliders"), "変化", 0, 1.5, 0.01, 2, () => layout.vary, v => {
    layout.vary = v;
    clearTimeout(layoutTimer);
    layoutTimer = setTimeout(() => { flowers.forEach(f => f.q && render(f)); save(); }, 120);
  })();

  let sel = null, flashTimer = null;
  // 選択の目印。花畑では、選んだ花と同じパラメータの花すべて
  const marksOf = f => GARDEN ? pieces.filter(p => p.fi === f.idx).map(p => p.mark) : [f.mark];
  function select(f, flash = false) {
    if (sel) marksOf(sel).forEach(m => m.classList.remove("flash"));
    sel = f; save();
    if (flash) {
      const ms = marksOf(f);
      ms.forEach(m => m.classList.add("flash"));
      clearTimeout(flashTimer); flashTimer = setTimeout(() => ms.forEach(m => m.classList.remove("flash")), 900);
    }
  }
  wrap.addEventListener("click", e => {
    const r = wrap.getBoundingClientRect();
    if (GARDEN) {
      // クリックした位置の花（重なっていれば小さい方）
      const x = (e.clientX - r.left) / r.width * S, y = (e.clientY - r.top) / r.height * CH;
      const hit = pieces.filter(p => Math.hypot(p.x - x, p.y - y) < p.r * 0.85).sort((a, b) => a.r - b.r)[0];
      if (hit) select(flowers[hit.fi], true);
      return;
    }
    const i = clip(Math.floor((e.clientX - r.left) / r.width * G), 0, G - 1), j = clip(Math.floor((e.clientY - r.top) / r.height * G), 0, G - 1);
    select(flowers[j * G + i], true);
  });
  wrap.addEventListener("keydown", e => {
    if (!sel || GARDEN) return;
    const d = { ArrowLeft: -1, ArrowRight: 1, ArrowUp: -G, ArrowDown: G }[e.key];
    if (d === undefined) return;
    e.preventDefault();
    const i = sel.idx + d;
    if (i >= 0 && i < N && !(Math.abs(d) === 1 && Math.floor(i / G) !== Math.floor(sel.idx / G))) select(flowers[i], true);
  });

  // 色彩 UI
  CONCEPTS.forEach((c, i) => {
    const lab = document.createElement("label");
    lab.title = c.name;
    lab.append(Object.assign(document.createElement("span"), { textContent: c.name }));
    const inp = Object.assign(document.createElement("input"), { type: "color", id: `each${i}` });
    inp.addEventListener("input", () => { color.each[i] = inp.value; color.eachDeep[i] = null; custom(); recolor(); });
    lab.append(inp); $("eachColors").append(lab);
  });
  function recolor() {
    $("sameColors").hidden = color.mode !== "same";
    $("eachColors").hidden = color.mode !== "each";
    buildLUT(); colorVer++; save(); requestPaint();
  }
  const colorShow = COLOR_SLIDERS.map(([k, label, lo, hi, st, dg]) =>
    slider($("colorSliders"), label, lo, hi, st, dg, () => color[k], v => { color[k] = v; recolor(); }));
  // 色のセットの選択肢（最後はカスタム）。色を手で変えるとカスタムになる
  COLOR_SETS.forEach(([name], i) => $("colorSet").append(new Option(name, i)));
  $("colorSet").append(new Option("カスタム", ""));
  $("colorSet").addEventListener("change", e => {
    if (e.target.value === "") { color.set = ""; save(); return; }
    applySet(+e.target.value); syncColor(); recolor();
  });
  const custom = () => { color.set = ""; $("colorSet").value = ""; };
  function syncColor() {
    for (const r of document.querySelectorAll("input[name=cmode]")) r.checked = r.value === color.mode;
    $("colorSet").value = color.set;
    $("base").value = color.base; $("bg").value = color.bg;
    $("deep").value = color.deep || rgb2hex(endOf(color.base, isLight(), null).map(v => v * 255));
    $("bgClear").checked = color.transparent; $("bg").disabled = color.transparent;
    color.each.forEach((c, i) => { $(`each${i}`).value = c; });
    colorShow.forEach(f => f());
  }
  for (const r of document.querySelectorAll("input[name=cmode]"))
    r.addEventListener("change", () => { if (r.checked) { color.mode = r.value; custom(); recolor(); } });
  for (const k of ["base", "bg", "deep"]) $(k).addEventListener("input", e => { color[k] = e.target.value; custom(); recolor(); });
  $("bgClear").addEventListener("change", e => { color.transparent = e.target.checked; $("bg").disabled = color.transparent; custom(); recolor(); });
  // 抽選した色は深い色を指定しない（芯の濃さで決める）
  const randomize = rng => { Object.assign(color, randomColor(rng), { deep: null, eachDeep: Array(9).fill(null), set: "" }); syncColor(); recolor(); };
  $("randColor").addEventListener("click", () => randomize(freshRng()));
  $("resetColor").addEventListener("click", () => {
    Object.assign(color, { ...COLOR_DEFAULT, mode: color.mode, each: [...SKY9], eachDeep: Array(9).fill(null) }); syncColor(); recolor();
  });

  // 操作
  $("rollAll").addEventListener("click", () => generate(newSeed()));
  const seedError = msg => { $("seedErr").textContent = msg || ""; $("seedErr").hidden = !msg; };
  const seedFromInput = () => {
    let s;
    try { s = parseSeed($("seedIn").value); } catch (e) { seedError(e.message); $("seedIn").focus(); return; }
    if (s === null) { $("seedIn").focus(); return; }
    seedError(); $("seedIn").value = ""; generate(s);
  };
  $("seedIn").addEventListener("input", () => seedError());
  $("seedCopy").addEventListener("click", async () => {
    if (seed === null) return;
    const btn = $("seedCopy"), text = pad12(seed);
    let ok = false;
    try { await navigator.clipboard.writeText(text); ok = true; } catch {
      const sel = getSelection(), r = document.createRange();
      r.selectNodeContents($("seedCur")); sel.removeAllRanges(); sel.addRange(r);
      try { ok = document.execCommand("copy"); } catch {}
    }
    btn.textContent = ok ? "コピー済み" : "選択しました";
    clearTimeout(btn._t); btn._t = setTimeout(() => { btn.textContent = "コピー"; }, 1500);
  });
  $("seedNow").addEventListener("click", () => { seedError(); generate(dateSeed(new Date())); });
  $("seedGo").addEventListener("click", seedFromInput);
  $("seedIn").addEventListener("keydown", e => { if (e.key === "Enter") seedFromInput(); });
  // 変奏：ほかの 8 つを、選んだ花と同じ種類にして、そのパラメータの近く（変化の大きさを花ごとに変える）で埋める。
  // 姿の変化はパラメータから決まるので、近いパラメータでも花びらの輪郭や層の構成は少しずつ違う姿になる。
  // 1 輪のときは、その花自身を近いパラメータで探索し直す
  $("variations").addEventListener("click", () => {
    if (!sel || !sel.q) return;
    const base = sel.q, c = sel.concept, list = G === 1 ? [sel] : flowers.filter(f => f !== sel);
    const base0 = newSeed();
    markEdited();
    list.forEach(f => { clearFlower(f); setConcept(f, sel.ci); });
    requestPaint();
    rollMany(list, f => {
      const r = seedRng(base0, f.idx), sc = 0.5 + 1.5 * list.indexOf(f) / Math.max(1, list.length - 1);
      return () => mutate(r, base, sc, c);
    });
  });

  // 保存：パソコンは Blob URL でダウンロード。タッチ端末はページ内に画像を出し、長押しか共有シートで保存する
  const touch = matchMedia("(pointer: coarse)").matches;
  let saveFile = null, saveUrl = null;
  // 画面左下と同じシード表示を画像にも描き込む（文字の大きさと余白は画像の幅に比例）
  function drawSeedLabel(c, W, H, size, x, y) {
    const label = $("seed").textContent;
    if (!label) return;
    c.font = `${Math.round(W * size)}px ui-monospace, SFMono-Regular, Menlo, monospace`;
    if ("letterSpacing" in c) c.letterSpacing = `${(W * 0.0004).toFixed(1)}px`;
    c.fillStyle = $("seed").style.color || "rgba(0, 0, 0, .3)";
    c.fillText(label, Math.round(x), Math.round(y));
  }
  function withSeedLabel() {
    const out = Object.assign(document.createElement("canvas"), { width: S, height: CH }), c = out.getContext("2d");
    c.drawImage(stillCanvas(), 0, 0);
    const p = seedPos();
    drawSeedLabel(c, S, S, 0.013, p.x, p.y);
    return out;
  }
  // 壁紙のサイズ（iPhone / Android、WP_SIZES はキャンバスの用意のところ）。選んだサイズは全ページ共通で覚えておく
  // 安全領域：スマホは画像を画面いっぱいに拡大してはみ出しを切るので（21:9 では左右、視差効果では周囲が切れる）、
  // ビジュアルは画像の幅の SAFE 倍に縮めて中央に置き、パターンのシードは幅の (1 − SAFE) / 2 以上内側に入れる
  const SAFE = 0.85;
  // 縦長 W × H px：背景で塗りつぶし、ビジュアル（正方形、一辺は幅の SAFE 倍）を上下左右の中央へ置く。
  // シードは画像の左下ではなく、ビジュアルの左下（正方形の PNG と同じ位置・同じ比率の大きさ）に入れる
  function wallpaper(W, H) {
    const out = Object.assign(document.createElement("canvas"), { width: W, height: H }), c = out.getContext("2d");
    const V = Math.round(W * SAFE), left = Math.round((W - V) / 2), top = Math.round((H - V) / 2);
    if (!color.transparent) { c.fillStyle = color.bg; c.fillRect(0, 0, W, H); }
    c.imageSmoothingQuality = "high";
    c.drawImage(stillCanvas(), left, top, V, V);
    const p = seedPos(), k = V / S;
    drawSeedLabel(c, V, V, 0.013, left + p.x * k, top + p.y * k);
    return out;
  }
  // 花畑の壁紙 W × H px：正方形を縮めて置くのではなく、壁紙の全体に花畑を並べ直して、その大きさで描く。
  // 並べ方は同じシード（系列 12）で W × H に並べたもの。シードは左下に、安全領域に収まるよう左端・下端から幅の (1 − SAFE) / 2 内側に入れる。
  // 描くのに数秒かかるので、少しずつ進めて progress(0〜1) で進み具合を知らせる
  async function gardenWallpaper(W, H, progress) {
    const list = gardenLayout(seed ?? 0, W, H).map(p => [p, flowers[p.fi]]).filter(([, f]) => f.q);
    const totals = list.map(([p]) => pieceTotal(pieceSize(p))), all = totals.reduce((a, b) => a + b, 0);
    let done = 0, last = performance.now();
    for (let i = 0; i < list.length; i++) {
      const [p, f] = list[i], run = plotter(p, f.q, f.concept, pieceSize(p), p.x, p.y, p.angle, p.salt);
      if (!run) { done += totals[i]; continue; }
      while (p.pts < totals[i]) {
        run(120000); done += 120000;
        if (performance.now() - last > 30) { progress?.(Math.min(1, done / all)); await yieldUI(); last = performance.now(); }
      }
    }
    const out = Object.assign(document.createElement("canvas"), { width: W, height: H }), c = out.getContext("2d");
    const im = c.createImageData(W, H);
    compose(list, W, H, new Float32Array(W * H * 3), im.data);
    c.putImageData(im, 0, 0);
    const m = W * (1 - SAFE) / 2;
    drawSeedLabel(c, W, W, 0.013, m, H - m);
    return out;
  }
  // PNG の tEXt チャンク（Latin-1 のみ）にシードを書き込む（IHDR の直後に挿入）
  const CRC = new Int32Array(256).map((_, n) => { for (let k = 0; k < 8; k++) n = n & 1 ? 0xEDB88320 ^ n >>> 1 : n >>> 1; return n; });
  function pngText(buf, entries) {
    const src = new Uint8Array(buf), parts = [src.subarray(0, 33)];
    for (const [key, val] of entries) {
      const data = new TextEncoder().encode(`${key}\0${val}`), ch = new Uint8Array(12 + data.length), dv = new DataView(ch.buffer);
      dv.setUint32(0, data.length); ch.set([116, 69, 88, 116], 4); ch.set(data, 8);
      let crc = -1;
      for (let i = 4; i < 8 + data.length; i++) crc = CRC[(crc ^ ch[i]) & 255] ^ crc >>> 8;
      dv.setUint32(8 + data.length, (crc ^ -1) >>> 0);
      parts.push(ch);
    }
    parts.push(src.subarray(33));
    return new Blob(parts, { type: "image/png" });
  }
  // 段階的に半分ずつ縮小してから目的の大きさにする（一度に大きく縮めると細い線がつぶれて粗くなるため）
  function downscale(src, w) {
    let cur = src;
    while (cur.width / 2 >= w) {
      const half = Object.assign(document.createElement("canvas"), { width: cur.width / 2 | 0, height: cur.height / 2 | 0 });
      const c = half.getContext("2d"); c.imageSmoothingQuality = "high"; c.drawImage(cur, 0, 0, half.width, half.height);
      cur = half;
    }
    const out = Object.assign(document.createElement("canvas"), { width: w, height: w }), c = out.getContext("2d");
    c.imageSmoothingQuality = "high"; c.drawImage(cur, 0, 0, w, w);
    return out;
  }
  // パターン壁紙 W × H px：今の 3 × 3 の 9 つの花を写して、横 3 ブロック（花 9 個）で敷き詰める。
  // ブロックごとに、9 つの並び順・花ごとの回転（90° 単位）・左右反転をシードの系列 11 で決める（同じシードなら同じ柄）。
  // 縦は欠けない段数（6 段）を上下中央に置く（端が画面で切れてもよい）。シードはパターンの左下に 1 つだけ入れ、
  // 安全領域に収まるよう、左端・下端から幅の (1 − SAFE) / 2 以上内側に置く
  const PT_COLS = 3;
  function pattern(W, H) {
    const B = W / PT_COLS, cell = B / 3, rows = Math.floor(H / B), y0 = Math.round((H - rows * B) / 2);
    const sheet = downscale(stillCanvas(), Math.round(cell * 3)), sc = sheet.width / 3;
    const out = Object.assign(document.createElement("canvas"), { width: W, height: H }), c = out.getContext("2d");
    if (!color.transparent) { c.fillStyle = color.bg; c.fillRect(0, 0, W, H); }
    const r = seedRng(seed ?? 0, 11);
    for (let by = 0; by < rows; by++) for (let bx = 0; bx < PT_COLS; bx++) {
      const perm = [...Array(9).keys()];
      for (let i = 8; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [perm[i], perm[j]] = [perm[j], perm[i]]; }
      perm.forEach((src, k) => {
        const rot = Math.floor(r() * 4), flip = r() < 0.5;
        const cx = bx * B + (k % 3 + 0.5) * cell, cy = y0 + by * B + (Math.floor(k / 3) + 0.5) * cell;
        c.save(); c.translate(cx, cy); c.rotate(rot * Math.PI / 2); if (flip) c.scale(-1, 1);
        c.drawImage(sheet, (src % 3) * sc, Math.floor(src / 3) * sc, sc, sc, -cell / 2, -cell / 2, cell, cell);
        c.restore();
      });
    }
    const m = W * (1 - SAFE) / 2;
    drawSeedLabel(c, W, W, 0.013, Math.max(W * 0.012, m), Math.min(y0 + rows * B + W * 0.03, H - m));
    return out;
  }
  // ファイル名はシード（1 輪は _1x1、縦長は _1320x2868 / _1440x3200、編集済みは _edited を付ける）
  function fileName(suffix) {
    const base = seed !== null ? pad12(seed) : "symbea_flower";
    return `${base}${edited ? "_edited" : ""}${GARDEN ? "_garden" : G === 1 ? "_1x1" : ""}${suffix}.png`;
  }
  function savePNG(out, name) {
    return new Promise(done => out.toBlob(async png => {
      if (!png) return done();
      const src = /^https?:$/.test(location.protocol) ? `${location.origin}${location.pathname}?seed=${pad12(seed)}` : "";
      const blob = seed === null ? png : pngText(await png.arrayBuffer(), [
        ["Title", "Symbea Flower"],
        ["Seed", pad12(seed) + (edited ? " (edited)" : "")],
        ["Source", !edited ? src : ""],
      ].filter(([, v]) => v));
      if (!touch) {
        // 続けて保存しても前のダウンロードが切れないよう、URL ごとに少し待ってから破棄する
        const url = URL.createObjectURL(blob), a = document.createElement("a");
        a.download = name; a.href = url; a.click();
        setTimeout(() => URL.revokeObjectURL(url), 30000);
        return done();
      }
      if (saveUrl) URL.revokeObjectURL(saveUrl);
      saveUrl = URL.createObjectURL(blob);
      saveFile = new File([blob], name, { type: "image/png" });
      $("saverImg").src = saveUrl;
      $("saverShare").hidden = !(navigator.canShare && navigator.canShare({ files: [saveFile] }));
      $("saver").hidden = false;
      done();
    }, "image/png"));
  }
  $("saveAll").addEventListener("click", () => savePNG(withSeedLabel(), fileName("")));
  // 花畑は壁紙の全体に並べ直して描く（数秒かかるので、作っている間はボタンに進み具合を出し、保存のボタンを押せなくする）
  let making = false;
  async function saveTall({ w, h }) {
    if (!GARDEN) return savePNG(wallpaper(w, h), fileName(`_${w}x${h}`));
    if (w === S && h === CH) return savePNG(withSeedLabel(), fileName(`_${w}x${h}`));   // 画面と同じ大きさ：見えているそのまま
    if (making) return;
    making = true;
    const btns = ["saveAll", "saveTall", "saveBoth"].map($).filter(Boolean), label = $("saveTall").textContent;
    btns.forEach(b => { b.disabled = true; });
    try {
      const out = await gardenWallpaper(w, h, t => { $("saveTall").textContent = `${w} × ${h} を作成中… ${Math.round(t * 100)}%`; });
      await savePNG(out, fileName(`_${w}x${h}`));
    } finally {
      making = false; btns.forEach(b => { b.disabled = false; }); $("saveTall").textContent = label;
    }
  }
  const savePattern = ({ w, h }) => savePNG(pattern(w, h), fileName(`_pattern_${w}x${h}`));
  // サイズの切り替え：ボタン名を選んだサイズに合わせる
  function syncSize() {
    const { w, h } = WP_SIZES[wpSize];
    document.querySelectorAll('input[name="wpsize"]').forEach(r => { r.checked = r.value === wpSize; });
    $("saveTall").textContent = `${w} × ${h} で保存`;
    if ($("savePattern")) $("savePattern").textContent = `パターン壁紙（${w} × ${h}）で保存`;
  }
  document.querySelectorAll('input[name="wpsize"]').forEach(r => r.addEventListener("change", () => {
    if (!r.checked || !WP_SIZES[r.value]) return;
    wpSize = r.value; store.set(WKEY, wpSize); syncSize();
    if (GARDEN) {                                  // 花畑は描画エリアを選んだ壁紙の大きさにして並べ直す
      const { w, h } = WP_SIZES[wpSize];
      sizeCanvas(w, h); relayout(); placeSeed(); flowers.forEach(f => f.q && render(f));
    }
  }));
  syncSize();
  $("saveTall").addEventListener("click", () => saveTall(WP_SIZES[wpSize]));
  if ($("savePattern")) $("savePattern").addEventListener("click", () => savePattern(WP_SIZES[wpSize]));
  // パソコンだけ：縦長・パターンの壁紙を 2 サイズとも続けてダウンロードする
  for (const [id, fn] of [["saveBoth", saveTall], ["savePatternBoth", savePattern]]) {
    if (!$(id)) continue;
    $(id).hidden = touch;
    $(id).addEventListener("click", async () => {
      for (const sz of Object.values(WP_SIZES)) await fn(sz);
    });
  }
  $("saverShare").addEventListener("click", () => { if (saveFile) navigator.share({ files: [saveFile] }).catch(() => {}); });
  const closeSaver = () => { $("saver").hidden = true; };
  $("saverClose").addEventListener("click", closeSaver);
  $("saver").addEventListener("click", e => { if (e.target === $("saver")) closeSaver(); });
  document.addEventListener("keydown", e => { if (e.key === "Escape" && !$("saver").hidden) closeSaver(); });

  document.querySelectorAll('input[name="motion"]').forEach(r => r.addEventListener("change", () => { if (r.checked) { layout.motionChosen = true; setMotion(r.value); } }));
  // 起動：URL の ?seed= を最優先。次に保存済みの花、どちらもなければ新しいシードで生成
  syncColor(); recolor();
  let urlSeed = null;
  try { urlSeed = parseSeed(new URLSearchParams(location.search).get("seed")); } catch (e) { seedError(`URL の ${e.message}`); }
  // 変奏のあとは同じ種類が並ぶので、種類の重複は許す
  const hasSaved = Array.isArray(saved.cells) && saved.cells.length === N &&
    saved.cells.every(c => c && Number.isInteger(c.ci) && c.ci >= 0 && c.ci < 9);
  flowers.forEach(f => setConcept(f, hasSaved ? saved.cells[f.idx].ci : f.idx));
  if (hasSaved) {
    saved.cells.forEach((s, i) => {
      const f = flowers[i];
      f.q = s.q || null;
    });
  }
  select(flowers[hasSaved ? clip(saved.sel | 0, 0, N - 1) : N >> 1]);
  if (urlSeed !== null && !(urlSeed === seed && !edited)) generate(urlSeed);
  else if (hasSaved && flowers.every(f => f.q)) { showSeed(); if (GARDEN) relayout(); flowers.forEach(render); }
  else generate(seed !== null && !edited ? seed : newSeed());
  setMotion(layout.motion === "dynamic" ? "dynamic" : "static");
  if (GARDEN) placeSeed();
  requestPaint();
})();
