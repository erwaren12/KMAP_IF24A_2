/*
 * app.js
 * Logika inti untuk Dashboard Aljabar Boolean & K-Map.
 * Dibuat tanpa library (Vanilla JS).
 * * Alur utama:
 * 1. (Input)   User memasukkan ekspresi ATAU minterm.
 * 2. (Parse)   Ekspresi diubah jadi token -> RPN (Shunting Yard).
 * 3. (Eval)    RPN/Minterm dievaluasi jadi Tabel Kebenaran & K-Map.
 * 4. (Simplify) Algoritma Quine-McCluskey (qmSimplify) dipakai untuk
 * menemukan SOP/POS dari K-Map.
 * 5. (Render)  Semua hasil (Tabel, K-Map, SOP/POS, Stats) ditampilkan ke UI.
 */

/* =======================
 * Utils & Definisi Global
 * ======================= */

// Konstanta Gray Code untuk urutan label K-Map.
const GRAY2 = [0, 1];
const GRAY4 = [0, 1, 3, 2]; // Urutan: 00, 01, 11, 10
const GRAY_STRINGS = {
    1: ['0', '1'],
    2: ['00', '01', '11', '10']
};

// Konteks variabel (A, B, C, D) berdasarkan jumlah (nVars)
const CONTEXT_VARS = {
    2: ['A', 'B'],
    3: ['A', 'B', 'C'],
    4: ['A', 'B', 'C', 'D']
};

// Utility (helper) singkat
const byId = (id) => document.getElementById(id);
const toBin = (n, w) => n.toString(2).padStart(w, '0');

// Mengambil variabel unik (A-Z) dari string, diurutkan.
function uniqueSortedVars(vars) {
    const set = new Set(vars.map(v => v.toUpperCase()));
    return Array.from(set).sort();
}
// Ekstrak variabel dari ekspresi mentah
function extractVars(expr) {
    const vars = (expr.match(/[A-Za-z]/g) || []).map(ch => ch.toUpperCase());
    return uniqueSortedVars(vars);
}

/* =======================
 * Tokenizer + Parser (Shunting-Yard)
 * ======================= */

// Mengubah string mentah (misal "A'B + C") menjadi array token
function tokenize(raw) {
    const src = raw.replace(/\s+/g, '');
    const tokens = [];
    let i = 0;
    while (i < src.length) {
        let ch = src[i];

        // Angka (0 atau 1)
        if (ch === '0' || ch === '1') {
            tokens.push({ type: 'NUM', value: Number(ch) }); i++;
            // Tangani NOT postfix (misal: 1')
            let negCount = 0; while (src[i] === "'") { negCount++; i++; }
            if (negCount % 2 === 1) tokens.push({ type: 'OP', value: 'NOT', unary: true, postfix: true, precedence: 4, associativity: 'right' });
            continue;
        }
        // Variabel (A-Z)
        if (/[A-Za-z]/.test(ch)) {
            const v = ch.toUpperCase(); tokens.push({ type: 'VAR', value: v }); i++;
            // Tangani NOT postfix (misal: A')
            let negCount = 0; while (src[i] === "'") { negCount++; i++; }
            if (negCount % 2 === 1) tokens.push({ type: 'OP', value: 'NOT', unary: true, postfix: true, precedence: 4, associativity: 'right' });
            continue;
        }
        // Kurung
        if (ch === '(') { tokens.push({ type: 'LP' }); i++; continue; }
        if (ch === ')') {
            tokens.push({ type: 'RP' }); i++;
             // Tangani NOT postfix setelah kurung (misal: (A+B)')
            let negCount = 0; while (src[i] === "'") { negCount++; i++; }
            if (negCount % 2 === 1) tokens.push({ type: 'OP', value: 'NOT', unary: true, postfix: true, precedence: 4, associativity: 'right' });
            continue;
        }
        // Operator Prefix (NOT)
        if (ch === '!' || ch === '~') { tokens.push({ type: 'OP', value: 'NOT', unary: true, prefix: true, precedence: 4, associativity: 'right' }); i++; continue; }
        // Operator Biner (AND, OR, XOR)
        if (ch === '&' || ch === '*' || ch === '.') { tokens.push({ type: 'OP', value: 'AND', precedence: 3, associativity: 'left' }); i++; continue; }
        if (ch === '+' || ch === '|') { tokens.push({ type: 'OP', value: 'OR', precedence: 1, associativity: 'left' }); i++; continue; }
        if (ch === '^') { tokens.push({ type: 'OP', value: 'XOR', precedence: 2, associativity: 'left' }); i++; continue; }

        throw new Error("Karakter tidak dikenali pada posisi " + i + ": '" + ch + "'");
    }
    return tokens;
}

// Helper untuk Shunting Yard: Cek token 'a' adalah akhir operand?
function endsOperand(tok) {
    return tok && (tok.type === 'VAR' || tok.type === 'NUM' || (tok.type === 'OP' && tok.postfix) || tok.type === 'RP');
}
// Helper untuk Shunting Yard: Cek token 'b' adalah awal operand?
function beginsOperand(tok) {
     return tok && (tok.type === 'VAR' || tok.type === 'NUM' || tok.type === 'LP' || (tok.type === 'OP' && tok.prefix));
}

// Implementasi Algoritma Shunting Yard (Dijkstra)
// Mengubah token infix (urutan normal) menjadi RPN (postfix/urutan terbalik)
function toRPN(tokens) {
    const output = []; // Antrian output (hasil RPN)
    const stack = [];  // Tumpukan operator sementara

    // Langkah 1: Sisipkan token AND implisit.
    const withImplicit = [];
    for (let i = 0; i < tokens.length; i++) {
        withImplicit.push(tokens[i]);
        const a = tokens[i], b = tokens[i + 1];
        if (endsOperand(a) && beginsOperand(b)) {
            withImplicit.push({ type: 'OP', value: 'AND', precedence: 3, associativity: 'left', implicit: true });
        }
    }

    // Langkah 2: Algoritma Shunting Yard standar
    for (let i = 0; i < withImplicit.length; i++) {
        const t = withImplicit[i];

        // Var/Num/NOT Postfix -> langsung ke output
        if (t.type === 'VAR' || t.type === 'NUM' || (t.type === 'OP' && t.postfix)) {
            output.push(t); continue;
        }
        // Operator Prefix (NOT) -> ke stack
        if (t.type === 'OP' && t.prefix) {
            stack.push(t); continue;
        }

        // Operator Biner (AND, OR, XOR)
        if (t.type === 'OP' && !t.unary) {
            while (stack.length) {
                const top = stack[stack.length - 1];
                if (top.type === 'OP' && top.type !== 'LP' && ( (top.precedence > t.precedence) || (top.precedence === t.precedence && t.associativity === 'left') )) {
                     output.push(stack.pop());
                } else break;
            }
            stack.push(t);
            continue;
        }

        // Kurung
        if (t.type === 'LP') { stack.push(t); continue; }
        if (t.type === 'RP') {
            while (stack.length && stack[stack.length - 1].type !== 'LP') {
                 output.push(stack.pop());
            }
            if (!stack.length || stack[stack.length - 1].type !== 'LP') {
                throw new Error("Kurung tidak seimbang (RP tanpa LP)");
            }
            stack.pop(); // Buang LP
            continue;
        }
    }

    // Pindahkan sisa operator
    while (stack.length) {
        const s = stack.pop();
        if (s.type === 'LP') throw new Error("Kurung tidak seimbang (sisa LP)");
        output.push(s);
    }
    return output;
}

// Mengevaluasi ekspresi RPN
function evalRPN(rpn, env) {
    const st = [];
    for (const t of rpn) {
        if (t.type === 'NUM') st.push(!!t.value);
        else if (t.type === 'VAR') {
            if (!(t.value in env)) { st.push(false); }
            else { st.push(!!env[t.value]); }
        }
        else if (t.type === 'OP') {
            if (t.value === 'NOT') {
                if (st.length < 1) throw new Error("Operator NOT kekurangan operand");
                const a = st.pop(); st.push(!a);
            }
            else {
                if (st.length < 2) throw new Error(`Operator ${t.value} kekurangan operand`);
                const b = st.pop(); const a = st.pop();
                if (t.value === 'AND') st.push(a && b);
                else if (t.value === 'OR') st.push(a || b);
                else if (t.value === 'XOR') st.push(Boolean(a) !== Boolean(b));
                else throw new Error("Operator tidak dikenal: " + t.value);
            }
        }
    }
    if (st.length !== 1) throw new Error("Ekspresi tidak valid (hasil akhir stack != 1)");
    return st[0] ? 1 : 0;
}


/* =======================
 * Quine–McCluskey (SOP) (Dengan Benchmark)
 * ======================= */
// Helper QM
function countOnes(binStr) { return binStr.split('').filter(c => c === '1').length; }
function canCombine(a, b) { let diff = 0; for (let i = 0; i < a.length; i++) { if (a[i] !== b[i]) diff++; if (diff > 1) return false; } return diff === 1; }
function combine(a, b) { let r = ''; for (let i = 0; i < a.length; i++) { r += (a[i] === b[i]) ? a[i] : '-'; } return r; }
function covers(imp, mintermBin) { for (let i = 0; i < imp.length; i++) { if (imp[i] === '-') continue; if (imp[i] !== mintermBin[i]) return false; } return true; }

// Fungsi utama QM
function qmSimplify(minterms, dontcares, varNames) {
    const t0 = performance.now(); // CATAT WAKTU MULAI
    dontcares = dontcares || [];
    if (!minterms.length && !dontcares.length) return { implicants: [], sop: '0', time: performance.now() - t0 };
    if (!minterms.length) return { implicants: [], sop: '0', time: performance.now() - t0 };
    const W = varNames.length;
    const minBins = minterms.map(m => toBin(m, W));
    const dcBins = dontcares.map(m => toBin(m, W));
    const allBins = [...new Set([...minBins, ...dcBins])];
    if (allBins.length === (1 << W) && dcBins.length < allBins.length) return { implicants: ['-'.repeat(W)], sop: '1', time: performance.now() - t0 };
    let groups = {};
    for (const b of allBins) { const k = countOnes(b); (groups[k] || (groups[k] = [])).push({ bin: b, used: false, from: [b] }); }
    let newGroups = {}; let anyCombined = true; const allCombinedLevels = [];
    while (anyCombined) {
        anyCombined = false; newGroups = {};
        const keys = Object.keys(groups).map(Number).sort((a, b) => a - b);
        for (let idx = 0; idx < keys.length - 1; idx++) {
            const k = keys[idx], k2 = keys[idx + 1];
            const g1 = groups[k] || [], g2 = groups[k2] || [];
            for (const a of g1) for (const b of g2) {
                if (canCombine(a.bin, b.bin)) {
                    const c = combine(a.bin, b.bin);
                    const ones = countOnes(c.replace(/-/g, ''));
                    const item = { bin: c, used: false, from: [...new Set([...(a.from || []), ...(b.from || [])])] };
                    (newGroups[ones] || (newGroups[ones] = [])).push(item);
                    a.used = true; b.used = true; anyCombined = true;
                }
            }
        }
        for (const k in newGroups) {
            const unique = []; const seen = new Set();
            for (const it of newGroups[k]) {
                const key = it.bin + '|' + (it.from || []).join(',');
                if (!seen.has(key)) { seen.add(key); unique.push(it); }
            }
            newGroups[k] = unique;
        }
        const primes = [];
        for (const k in groups) for (const it of groups[k]) if (!it.used) primes.push(it.bin);
        allCombinedLevels.push(primes);
        groups = newGroups;
    }
    const finalPrimes = new Set();
    for (const arr of allCombinedLevels) for (const p of arr) finalPrimes.add(p);
    for (const k in groups) for (const it of groups[k]) finalPrimes.add(it.bin);
    const primeList = Array.from(finalPrimes);
    const minBin = minBins; const cover = {};
    for (let i = 0; i < minBin.length; i++) { cover[i] = []; for (let j = 0; j < primeList.length; j++) if (covers(primeList[j], minBin[i])) cover[i].push(j); }
    const chosen = new Set(); const coveredRows = new Set();
    for (let i = 0; i < minBin.length; i++) if (cover[i].length === 1) chosen.add(cover[i][0]);
    const markCovered = () => { let changed = false; for (let i = 0; i < minBin.length; i++) { if (coveredRows.has(i)) continue; for (const j of (cover[i] || [])) { if (chosen.has(j)) { coveredRows.add(i); changed = true; break; } } } return changed; };
    markCovered();
    while (coveredRows.size < minBin.length) {
        let bestJ = -1, bestCover = -1;
        for (let j = 0; j < primeList.length; j++) if (!chosen.has(j)) {
            let c = 0; for (let i = 0; i < minBin.length; i++) if (!coveredRows.has(i) && cover[i].includes(j)) c++;
            if (c > bestCover) { bestCover = c; bestJ = j; }
        }
        if (bestJ === -1) break;
        chosen.add(bestJ); markCovered();
    }
    const implicants = Array.from(chosen).map(j => primeList[j]);
    const sop = implicantsToSOP(implicants, varNames);
    const t1 = performance.now(); // CATAT WAKTU SELESAI
    return { implicants, sop, time: t1 - t0 };
}

// Konversi implicant ke string SOP
function implicantsToSOP(impls, vars) {
    if (!impls.length) return '0';
    if (impls.some(mask => mask.split('').every(c => c === '-'))) return '1';
    const parts = impls.map(mask => {
        let s = ''; for (let i = 0; i < mask.length; i++) { if (mask[i] === '-') continue; const v = vars[i]; s += (mask[i] === '1') ? v : (v + "'"); } return s;
    }).filter(Boolean);
    return parts.join(' + ');
}


/* =======================
 * K-Map Logic & Rendering
 * ======================= */
function kmapLayoutForVars(nVars) {
    if (nVars === 1) return { rows: GRAY2, cols: [0], rowVars: ['A'], colVars: [], index(rc) { return GRAY2[rc.r]; } };
    if (nVars === 2) return { rows: GRAY2, cols: GRAY2, rowVars: ['A'], colVars: ['B'], index({ r, c }) { const A = GRAY2[r], B = GRAY2[c]; return (A << 1) | B; } };
    if (nVars === 3) return { rows: GRAY2, cols: GRAY4, rowVars: ['A'], colVars: ['B', 'C'], index({ r, c }) { const A = GRAY2[r], BC = GRAY4[c]; const B = (BC >> 1) & 1, C = BC & 1; return (A << 2) | (B << 1) | C; } };
    if (nVars === 4) return { rows: GRAY4, cols: GRAY4, rowVars: ['A', 'B'], colVars: ['C', 'D'], index({ r, c }) { const AB = GRAY4[r], CD = GRAY4[c]; const A = (AB >> 1) & 1, B = AB & 1, C = (CD >> 1) & 1, D = CD & 1; return (A << 3) | (B << 2) | (C << 1) | D; } };
    return null;
}

function buildTruthTable(vars, rpn, mintermSet = null) {
    const rows = []; const n = vars.length; const total = 1 << n;
    const useMintermSet = (mintermSet instanceof Set);
    for (let m = 0; m < total; m++) {
        const env = {};
        for (let i = 0; i < n; i++) env[vars[i]] = (m >> (n - 1 - i)) & 1;
        let y;
        if (useMintermSet) { y = mintermSet.has(m) ? 1 : 0; }
        else { y = rpn ? evalRPN(rpn, env) : 0; }
        rows.push({ m, env, y });
    }
    return rows;
}

/* =======================
 * App State & Wiring
 * ======================= */
const els = {
    expr: byId('expr'),
    btnEval: byId('btn-eval'),
    btnClear: byId('btn-clear'),
    varsPill: byId('vars-pill'),
    mintermsPill: byId('minterms-pill'),
    simpPill: byId('simp-pill'),
    ttHead: byId('ttbl').querySelector('thead'),
    ttBody: byId('ttbl').querySelector('tbody'),
    kmapContainer: byId('kmap-container'),
    kmapCorner: byId('kmap-corner'),
    kmapLabelTop: byId('kmap-label-top'),
    kmapLabelLeft: byId('kmap-label-left'),
    kmap: byId('kmap'),
    btnSimplifySOP: byId('btn-simplify-sop'),
    btnSimplifyPOS: byId('btn-simplify-pos'),
    btnReset: byId('btn-reset'),
    outSimplified: byId('out-simplified'),
    mintermIO: byId('minterm-io'),
    btnImport: byId('btn-import'),
    btnExport: byId('btn-export'),
    errorBox: byId('error-box'),
    themeToggle: byId('theme-toggle-cb'),
    btnPrint: byId('btn-print'), // Tombol Cetak/PDF
    btnDownloadPng: byId('btn-download-png'), // Tombol Download PNG
    benchmarkPill: byId('benchmark-pill'),
    themeToggleLabel: byId('theme-toggle-label')
};

let currentKMap = { vars: [], n: 0, layout: null, cells: [], total: 0 };
let currentRPN = null;

function setPills(vars, minterms, sop, benchmark) {
    els.varsPill.textContent = `${vars.length ? vars.join(', ') : '—'}`;
    els.mintermsPill.textContent = `${minterms.length ? minterms.join(',') : '—'}`;
    els.simpPill.textContent = `${sop || '—'}`;
    els.benchmarkPill.textContent = (benchmark === undefined) ? '—' : `${benchmark.toFixed(2)} ms`;
}

function renderTruthTable(vars, rows) {
    const thv = vars.map(v => `<th>${v}</th>`).join('');
    els.ttHead.innerHTML = `<tr>${thv}<th>Y</th><th class="muted">m</th></tr>`;
    const bodyHtml = rows.map(r => {
        const vs = vars.map(v => `<td>${r.env[v]}</td>`).join('');
        return `<tr>${vs}<td><b>${r.y}</b></td><td class="muted">${r.m}</td></tr>`;
    }).join('');
    els.ttBody.innerHTML = bodyHtml;
}

function initKMap(nVars, varNames) {
    const layout = kmapLayoutForVars(nVars);
    if (!layout) { els.kmap.innerHTML = `<div class="muted">Layout K-Map tidak valid.</div>`; return; }
    currentKMap = { vars: varNames, n: nVars, layout: layout, cells: new Array(1 << nVars).fill(0), total: (1 << nVars) };
    els.kmapCorner.innerHTML = ''; els.kmapLabelTop.innerHTML = ''; els.kmapLabelLeft.innerHTML = ''; els.kmap.innerHTML = '';
    const rowLabel = layout.rowVars.join(''); const colLabel = layout.colVars.join('');
    els.kmapCorner.textContent = `${rowLabel}\\${colLabel}`;
    const colStrings = GRAY_STRINGS[layout.colVars.length] || GRAY_STRINGS[1];
    els.kmapLabelTop.style.gridTemplateColumns = `repeat(${layout.cols.length}, 56px)`;
    for (let c = 0; c < layout.cols.length; c++) { const div = document.createElement('div'); div.className = 'kmap-axis-label'; div.textContent = colStrings[c]; els.kmapLabelTop.appendChild(div); }
    const rowStrings = GRAY_STRINGS[layout.rowVars.length] || GRAY_STRINGS[1];
    els.kmapLabelLeft.style.gridTemplateRows = `repeat(${layout.rows.length}, 44px)`;
    for (let r = 0; r < layout.rows.length; r++) { const div = document.createElement('div'); div.className = 'kmap-axis-label'; div.textContent = rowStrings[r]; els.kmapLabelLeft.appendChild(div); }
    els.kmap.style.gridTemplateColumns = `repeat(${layout.cols.length}, 56px)`;
    const cellsHtml = [];
    for (let r = 0; r < layout.rows.length; r++) { for (let c = 0; c < layout.cols.length; c++) { const idx = layout.index({ r, c }); cellsHtml.push(`<div class="kcell" data-index="${idx}" title="m${idx}">0</div>`); } }
    els.kmap.innerHTML = cellsHtml.join('');
}

function setupKMapUI(nVars) {
    const kmapVars = CONTEXT_VARS[nVars];
    initKMap(nVars, kmapVars);
    els.expr.value = ''; currentRPN = null; els.ttHead.innerHTML = ''; els.ttBody.innerHTML = ''; els.outSimplified.textContent = '—';
    setPills(kmapVars, [], '—', undefined); els.mintermIO.value = ''; els.errorBox.style.display = 'none';
}

function paintKMapFromMinterms(minterms) {
    if (!currentKMap.layout) return;
    const mintermSet = new Set(minterms);
    const children = els.kmap.children;
    for (let k = 0; k < children.length; k++) {
        const cell = children[k]; const idx = Number(cell.dataset.index);
        const isOne = mintermSet.has(idx);
        currentKMap.cells[idx] = isOne ? 1 : 0;
        cell.classList.remove('dont-care'); cell.classList.toggle('on', isOne); cell.textContent = isOne ? '1' : '0';
    }
}

function collectMintermsFromKMap() { const res = []; for (let i = 0; i < currentKMap.total; i++) if (currentKMap.cells[i] === 1) res.push(i); return res.sort((a, b) => a - b); }
function collectDontCaresFromKMap() { const res = []; for (let i = 0; i < currentKMap.total; i++) if (currentKMap.cells[i] === 2) res.push(i); return res.sort((a, b) => a - b); }
function collectMaxtermsFromKMap() { const res = []; for (let i = 0; i < currentKMap.total; i++) if (currentKMap.cells[i] === 0) res.push(i); return res.sort((a, b) => a - b); }

function implicantsToPOS(impls, vars) {
    if (!impls.length) return '1'; if (impls.some(mask => mask.split('').every(c => c === '-'))) return '0';
    const parts = impls.map(mask => { const literals = []; for (let i = 0; i < mask.length; i++) { if (mask[i] === '-') continue; const v = vars[i]; literals.push((mask[i] === '1') ? (v + "'") : v); } if (literals.length === 0) return null; if (literals.length === 1) return literals[0]; return `(${literals.join(' + ')})`; }).filter(Boolean);
    return parts.join('');
}

function simplifyFromKMap(mode = 'SOP') {
    const n = currentKMap.n, vars = currentKMap.vars; let resultString; let execTime = 0;
    if (n === 0) { const v = currentKMap.cells[0] || 0; resultString = (v === 1) ? '1' : '0'; }
    else { const dcs = collectDontCaresFromKMap(); if (mode === 'POS') { const maxterms = collectMaxtermsFromKMap(); const { implicants, time } = qmSimplify(maxterms, dcs, vars); resultString = implicantsToPOS(implicants, vars); execTime = time; } else { const minterms = collectMintermsFromKMap(); const { sop, time } = qmSimplify(minterms, dcs, vars); resultString = sop; execTime = time; } }
    els.outSimplified.textContent = resultString;
    return { resultString: resultString, time: execTime };
}

// ===========================================
// === Fungsi Baru: Generate K-Map SVG ===
// ===========================================
function generateKMapSVG() {
    const kmapState = currentKMap;
    if (!kmapState || !kmapState.layout || kmapState.n === 0) { throw new Error("K-Map state is not valid for SVG generation."); }
    const layout = kmapState.layout; const nVars = kmapState.n; const cells = kmapState.cells;
    const cellWidth = 60; const cellHeight = 48; const labelSize = 30; const gap = 6; const padding = 10;
    const cornerLabel = `${layout.rowVars.join('')}\\${layout.colVars.join('')}`;
    const colStrings = GRAY_STRINGS[layout.colVars.length] || GRAY_STRINGS[1];
    const rowStrings = GRAY_STRINGS[layout.rowVars.length] || GRAY_STRINGS[1];
    const numCols = layout.cols.length || 1; const numRows = layout.rows.length || 1;
    const mapWidth = numCols * cellWidth + (numCols - 1) * gap; const mapHeight = numRows * cellHeight + (numRows - 1) * gap;
    const svgWidth = labelSize + gap + mapWidth + 2 * padding; const svgHeight = labelSize + gap + mapHeight + 2 * padding;
    const styles = ` .kmap-svg { background-color: #222222; font-family: system-ui, sans-serif; } .kmap-label, .kmap-corner-label { font-size: 11px; fill: #aaaaaa; text-anchor: middle; dominant-baseline: middle; font-weight: 600; } .kmap-cell-rect { stroke: #313131; stroke-width: 1; rx: 6; } .kmap-cell-text { font-size: 16px; font-weight: 600; fill: #f1f1f1; text-anchor: middle; dominant-baseline: central; } .kmap-cell-minterm { font-size: 10px; fill: #aaaaaa; text-anchor: middle; dominant-baseline: hanging; } .kmap-cell-rect.on { fill: #2b966a; } .kmap-cell-rect.off { fill: #2a2a2a; } .kmap-cell-rect.dont-care { fill: #6b4220; stroke: #9c5b25; } .kmap-cell-text.on { fill: #ffffff; } .kmap-cell-text.dont-care { fill: #e8eefc; font-style: italic; } `;
    let svg = `<svg width="${svgWidth}" height="${svgHeight}" xmlns="http://www.w3.org/2000/svg">`; svg += `<style>${styles}</style>`; svg += `<rect width="100%" height="100%" class="kmap-svg"/>`; svg += `<g transform="translate(${padding}, ${padding})">`; svg += `<text x="${labelSize / 2}" y="${labelSize / 2}" class="kmap-corner-label">${cornerLabel}</text>`;
    for (let c = 0; c < numCols; c++) { const x = labelSize + gap + c * (cellWidth + gap) + cellWidth / 2; const y = labelSize / 2; svg += `<text x="${x}" y="${y}" class="kmap-label">${colStrings[c]}</text>`; }
    for (let r = 0; r < numRows; r++) { const x = labelSize / 2; const y = labelSize + gap + r * (cellHeight + gap) + cellHeight / 2; svg += `<text x="${x}" y="${y}" class="kmap-label">${rowStrings[r]}</text>`; }
    for (let r = 0; r < numRows; r++) { for (let c = 0; c < numCols; c++) { const idx = layout.index({ r, c }); const cellValue = cells[idx]; const x = labelSize + gap + c * (cellWidth + gap); const y = labelSize + gap + r * (cellHeight + gap); let cellClass = 'off'; let cellText = '0'; if (cellValue === 1) { cellClass = 'on'; cellText = '1'; } else if (cellValue === 2) { cellClass = 'dont-care'; cellText = 'd'; } svg += `<rect x="${x}" y="${y}" width="${cellWidth}" height="${cellHeight}" class="kmap-cell-rect ${cellClass}"/>`; svg += `<text x="${x + cellWidth / 2}" y="${y + cellHeight / 2 - 4}" class="kmap-cell-text ${cellClass}">${cellText}</text>`; svg += `<text x="${x + cellWidth / 2}" y="${y + cellHeight / 2 + 8}" class="kmap-cell-minterm"> ${idx}</text>`; } }
    svg += `</g>`; svg += `</svg>`; return svg;
}


/* =======================
 * Event Listeners (Pengatur Interaksi UI)
 * ======================= */
els.btnEval.addEventListener('click', () => { try { els.errorBox.style.display = 'none'; const expr = els.expr.value.trim(); if (!expr) throw new Error('Masukkan ekspresi.'); const detectedVars = extractVars(expr); let nVars; if (detectedVars.length > 0) { if (detectedVars.includes('D')) nVars = 4; else if (detectedVars.includes('C')) nVars = 3; else nVars = 2; } else { nVars = currentKMap.n || 3; } const kmapVars = CONTEXT_VARS[nVars]; const invalidVars = detectedVars.filter(v => !kmapVars.includes(v)); if (invalidVars.length > 0) { throw new Error(`Variabel '${invalidVars.join(',')}' tidak ada dalam konteks K-Map ${nVars}-variabel.`); } const tokens = tokenize(expr); currentRPN = toRPN(tokens); const rows = buildTruthTable(kmapVars, currentRPN, null); renderTruthTable(kmapVars, rows); const minFull = rows.filter(r => r.y === 1).map(r => r.m); initKMap(nVars, kmapVars); paintKMapFromMinterms(minFull); const { resultString: sop, time } = simplifyFromKMap('SOP'); setPills(kmapVars, minFull, sop, time); els.mintermIO.value = minFull.join(','); } catch (e) { console.error("Evaluation Error:", e); els.errorBox.textContent = "Kesalahan: " + e.message; els.errorBox.style.display = 'block'; } });
// Tombol BERSIHKAN: Reset semua
els.btnClear.addEventListener('click', () => {
    // 1. Gambar struktur K-Map 3 variabel default (kosong)
    //    (Meniru logika inisialisasi di akhir file)
    const initialNVars = 3;
    const initialKMapVars = CONTEXT_VARS[initialNVars];
    initKMap(initialNVars, initialKMapVars);

    // 2. Set panel statistik ke keadaan kosong/default
    setPills([], [], '—', undefined); // <-- Ini akan mengosongkan Konteks Variabel

    // 3. Pastikan input/output lain juga kosong
    els.expr.value = '';
    currentRPN = null;
    els.ttHead.innerHTML = '';
    els.ttBody.innerHTML = '';
    els.outSimplified.textContent = '—';
    els.mintermIO.value = '';
    els.errorBox.style.display = 'none';
});
els.expr.addEventListener('keydown', (event) => { if (event.key === 'Enter') { event.preventDefault(); els.btnEval.click(); } });
els.btnReset.addEventListener('click', () => { paintKMapFromMinterms([]); els.outSimplified.textContent = '—'; els.mintermIO.value = ''; els.expr.value = ''; setPills(currentKMap.vars, [], '—', undefined); });
els.btnSimplifySOP.addEventListener('click', () => { const { resultString: sop, time } = simplifyFromKMap('SOP'); els.expr.value = sop; const minterms = collectMintermsFromKMap(); setPills(currentKMap.vars, minterms, sop, time); });
els.btnSimplifyPOS.addEventListener('click', () => { const { resultString: pos, time } = simplifyFromKMap('POS'); els.expr.value = pos; const minterms = collectMintermsFromKMap(); setPills(currentKMap.vars, minterms, pos, time); });
els.kmap.addEventListener('click', (e) => { const cell = e.target.closest('.kcell'); if (!cell) return; const idx = Number(cell.dataset.index); if (isNaN(idx)) return; const newVal = (currentKMap.cells[idx] + 1) % 3; currentKMap.cells[idx] = newVal; cell.classList.toggle('on', newVal === 1); cell.classList.toggle('dont-care', newVal === 2); cell.textContent = (newVal === 2) ? 'd' : String(newVal); });
els.btnImport.addEventListener('click', () => { try { els.errorBox.style.display = 'none'; const txt = els.mintermIO.value.trim(); const parts = txt.split(/[,\s]+/).map(s => s.trim()).filter(Boolean).map(Number).filter(n => Number.isInteger(n) && n >= 0); if (!parts.length) { const nVars = currentKMap.n || 3; const kmapVars = CONTEXT_VARS[nVars]; paintKMapFromMinterms([]); const { resultString: sop, time } = simplifyFromKMap('SOP'); els.expr.value = sop; setPills(kmapVars, [], sop, time); const rows = buildTruthTable(kmapVars, null, new Set()); renderTruthTable(kmapVars, rows); return; } const maxMinterm = Math.max(...parts); let nVars; if (maxMinterm < 4) nVars = 2; else if (maxMinterm < 8) nVars = 3; else if (maxMinterm < 16) nVars = 4; else throw new Error(`Minterm '${maxMinterm}' terlalu besar (Maks 15).`); const kmapVars = CONTEXT_VARS[nVars]; if (nVars !== currentKMap.n) { initKMap(nVars, kmapVars); } const finalParts = parts.filter(n => n < (1 << nVars)); const mintermSet = new Set(finalParts); currentRPN = null; const rows = buildTruthTable(kmapVars, null, mintermSet); renderTruthTable(kmapVars, rows); paintKMapFromMinterms(finalParts); const { resultString: sop, time } = simplifyFromKMap('SOP'); els.expr.value = sop; setPills(kmapVars, finalParts.sort((a,b) => a-b), sop, time); } catch (e) { console.error("Import Error:", e); els.errorBox.textContent = "Kesalahan: " + e.message; els.errorBox.style.display = 'block'; } });
els.btnExport.addEventListener('click', () => { const ms = collectMintermsFromKMap(); const dcs = collectDontCaresFromKMap(); const all = [...new Set([...ms, ...dcs])].sort((a, b) => a - b); els.mintermIO.value = all.join(','); const { resultString: sop, time } = simplifyFromKMap('SOP'); els.expr.value = sop; setPills(currentKMap.vars, ms, sop, time); });
els.themeToggle.addEventListener('change', () => { const isLightMode = els.themeToggle.checked; document.body.classList.toggle('light-mode', isLightMode); });

// ===========================================
// === Fungsi Download PNG K-Map (SVG -> Canvas) ===
// ===========================================
els.btnDownloadPng.addEventListener('click', () => {
    try {
        const svgString = generateKMapSVG();
        const svgBase64 = btoa(unescape(encodeURIComponent(svgString)));
        const svgDataUrl = `data:image/svg+xml;base64,${svgBase64}`;
        const img = new Image();
        img.onload = () => {
            const canvas = document.createElement('canvas');
            canvas.width = img.width; canvas.height = img.height;
            const ctx = canvas.getContext('2d');
            ctx.drawImage(img, 0, 0);
            const pngDataUrl = canvas.toDataURL('image/png');
            const link = document.createElement('a');
            link.download = 'karnaugh_map.png'; link.href = pngDataUrl; link.click();
        };
        img.onerror = (err) => { console.error("Gagal memuat SVG ke Image:", err); alert("Gagal membuat gambar K-Map. Kesalahan saat memuat SVG."); };
        img.src = svgDataUrl;
    } catch (e) { console.error("Gagal generate/download K-Map SVG:", e); alert("Gagal membuat gambar K-Map: " + e.message); }
});

// ===========================================
// === Fungsi Cetak/PDF K-Map ===
// ===========================================
els.btnPrint.addEventListener('click', () => {
    window.print();
});

// Fungsi untuk memuat contoh ekspresi
const loadExample = (expr) => { els.expr.value = expr; els.btnEval.click(); }
byId('btn-ex1').addEventListener('click', () => loadExample("A'B + AC")); byId('btn-ex2').addEventListener('click', () => loadExample("A(B+C)")); byId('btn-ex3').addEventListener('click', () => loadExample("(A^B)C + A'B'")); byId('btn-ex4').addEventListener('click', () => loadExample("(A+B)(C+D)")); byId('btn-ex5').addEventListener('click', () => loadExample("A'B'+AB")); byId('btn-ex6').addEventListener('click', () => loadExample("A^B^C")); byId('btn-ex7').addEventListener('click', () => loadExample("(A+B'C')(A'+C)")); byId('btn-ex8').addEventListener('click', () => loadExample("(AB)'+C")); byId('btn-ex9').addEventListener('click', () => loadExample("AB+AC+BC")); byId('btn-ex10').addEventListener('click', () => loadExample("(A+B+C)(A'+B)(B+C')"));

/* =======================
 * Inisialisasi Aplikasi Saat Memuat
 * ======================= */
const initialNVars = 3; const initialKMapVars = CONTEXT_VARS[initialNVars]; initKMap(initialNVars, initialKMapVars);
setPills([], [], '—', undefined);
els.expr.value = ''; currentRPN = null; els.ttHead.innerHTML = ''; els.ttBody.innerHTML = ''; els.outSimplified.textContent = '—'; els.mintermIO.value = ''; els.errorBox.style.display = 'none';