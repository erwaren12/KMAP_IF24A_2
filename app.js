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
// Ini penting agar sel yang bersebelahan only beda 1 bit.
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
    const src = raw.replace(/\s+/g, ''); // Hapus semua spasi
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
    // Ini adalah 'bumbu' utama agar "AB" bisa dibaca sebagai "A AND B".
    // Logika: jika token 'a' adalah AKHIR operand dan token 'b' adalah AWAL operand,
    // sisipkan 'AND' di antara keduanya.
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
            // Selama operator di stack > prioritasnya, pindahkan ke output
            while (stack.length) {
                const top = stack[stack.length - 1];
                if (top.type === 'OP' && top.type !== 'LP' && ( (top.precedence > t.precedence) || (top.precedence === t.precedence && t.associativity === 'left') )) {
                     output.push(stack.pop());
                } else break;
            }
            stack.push(t); // Masukkan operator saat ini ke stack
            continue;
        }

        // Kurung
        if (t.type === 'LP') { stack.push(t); continue; }
        if (t.type === 'RP') {
            // Pindahkan operator dari stack ke output sampai ketemu LP
            while (stack.length && stack[stack.length - 1].type !== 'LP') {
                 output.push(stack.pop());
            }
            if (!stack.length || stack[stack.length - 1].type !== 'LP') {
                throw new Error("Kurung tidak seimbang (RP tanpa LP)");
            }
            stack.pop(); // Buang kurung buka (LP)
            continue;
        }
    }

    // Pindahkan sisa operator di stack ke output
    while (stack.length) {
        const s = stack.pop();
        if (s.type === 'LP') throw new Error("Kurung tidak seimbang (sisa LP)");
        output.push(s);
    }
    return output;
}

// Mengevaluasi ekspresi RPN
// 'env' (environment) adalah objek nilai variabel, misal: { A: 1, B: 0, C: 1 }
function evalRPN(rpn, env) {
    const st = []; // Stack nilai
    for (const t of rpn) {
        if (t.type === 'NUM') st.push(!!t.value);
        else if (t.type === 'VAR') {
            // Jika var tidak ada di env (misal ekspresi "A" di konteks A,B), anggap 0
            if (!(t.value in env)) {
                 st.push(false);
            } else {
                 st.push(!!env[t.value]);
            }
        }
        // Operator
        else if (t.type === 'OP') {
            if (t.value === 'NOT') {
                if (st.length < 1) throw new Error("Operator NOT kekurangan operand");
                const a = st.pop(); st.push(!a);
            }
            // Operator Biner
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
    return st[0] ? 1 : 0; // Kembalikan 1 atau 0
}


/* =======================
 * Quine–McCluskey (SOP) (Dengan Benchmark)
 * ======================= */

// Ini adalah inti dari fitur simplifikasi.
// Implementasi algoritma Quine-McCluskey untuk menemukan
// Prime Implicants, diikuti greedy cover untuk menemukan
// Essential Prime Implicants.
// Di-benchmark menggunakan performance.now().

// Helper QM
function countOnes(binStr) { return binStr.split('').filter(c => c === '1').length; }
function canCombine(a, b) { let diff = 0; for (let i = 0; i < a.length; i++) { if (a[i] !== b[i]) diff++; if (diff > 1) return false; } return diff === 1; }
function combine(a, b) { let r = ''; for (let i = 0; i < a.length; i++) { r += (a[i] === b[i]) ? a[i] : '-'; } return r; }
function covers(imp, mintermBin) { for (let i = 0; i < imp.length; i++) { if (imp[i] === '-') continue; if (imp[i] !== mintermBin[i]) return false; } return true; }

// Fungsi utama QM
function qmSimplify(minterms, dontcares, varNames) {
    const t0 = performance.now(); // CATAT WAKTU MULAI

    dontcares = dontcares || [];
    // Kasus-kasus dasar (return cepat)
    if (!minterms.length && !dontcares.length) return { implicants: [], sop: '0', time: performance.now() - t0 };
    if (!minterms.length) return { implicants: [], sop: '0', time: performance.now() - t0 };

    const W = varNames.length;
    const minBins = minterms.map(m => toBin(m, W));
    const dcBins = dontcares.map(m => toBin(m, W));
    const allBins = [...new Set([...minBins, ...dcBins])];

    // Jika semua sel (termasuk 'd') adalah 1, hasil = 1
    if (allBins.length === (1 << W) && dcBins.length < allBins.length) return { implicants: ['-'.repeat(W)], sop: '1', time: performance.now() - t0 };

    // Langkah 1: Kelompokkan berdasarkan jumlah angka '1'
    let groups = {};
    for (const b of allBins) { const k = countOnes(b); (groups[k] || (groups[k] = [])).push({ bin: b, used: false, from: [b] }); }

    // Langkah 2: Kombinasikan grup secara rekursif
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
        // Kumpulkan implicant prima (yang tidak bisa dikombinasi lagi)
        const primes = [];
        for (const k in groups) for (const it of groups[k]) if (!it.used) primes.push(it.bin);
        allCombinedLevels.push(primes);
        groups = newGroups;
    }
    const finalPrimes = new Set();
    for (const arr of allCombinedLevels) for (const p of arr) finalPrimes.add(p);
    for (const k in groups) for (const it of groups[k]) finalPrimes.add(it.bin);
    const primeList = Array.from(finalPrimes);

    // Langkah 3: Buat tabel Petrick / Greedy Cover
    const minBin = minBins; const cover = {};
    for (let i = 0; i < minBin.length; i++) { cover[i] = []; for (let j = 0; j < primeList.length; j++) if (covers(primeList[j], minBin[i])) cover[i].push(j); }

    // Langkah 4: Pilih Essential Prime Implicants (EPI)
    const chosen = new Set(); const coveredRows = new Set();
    for (let i = 0; i < minBin.length; i++) if (cover[i].length === 1) chosen.add(cover[i][0]);

    const markCovered = () => { let changed = false; for (let i = 0; i < minBin.length; i++) { if (coveredRows.has(i)) continue; for (const j of (cover[i] || [])) { if (chosen.has(j)) { coveredRows.add(i); changed = true; break; } } } return changed; };
    markCovered();

    // Langkah 5: Greedy cover untuk minterm sisanya
    while (coveredRows.size < minBin.length) {
        let bestJ = -1, bestCover = -1;
        for (let j = 0; j < primeList.length; j++) if (!chosen.has(j)) {
            let c = 0; for (let i = 0; i < minBin.length; i++) if (!coveredRows.has(i) && cover[i].includes(j)) c++;
            if (c > bestCover) { bestCover = c; bestJ = j; }
        }
        if (bestJ === -1) break; // Tidak ada lagi yg bisa dipilih
        chosen.add(bestJ); markCovered();
    }

    // Langkah 6: Konversi hasil ke string SOP
    const implicants = Array.from(chosen).map(j => primeList[j]);
    const sop = implicantsToSOP(implicants, varNames);

    const t1 = performance.now(); // CATAT WAKTU SELESAI
    return { implicants, sop, time: t1 - t0 };
}

// Konversi array implicant (misal: ['-10', '1-1']) ke string SOP (misal: "BC' + AC")
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

// Fungsi 'ajaib' yang mendefinisikan layout K-Map (baris, kolom, label,
// dan fungsi 'index' untuk mapping (r,c) ke minterm index).
function kmapLayoutForVars(nVars) {
    if (nVars === 1) return { rows: GRAY2, cols: [0], rowVars: ['A'], colVars: [], index(rc) { return GRAY2[rc.r]; } };
    if (nVars === 2) return { rows: GRAY2, cols: GRAY2, rowVars: ['A'], colVars: ['B'], index({ r, c }) { const A = GRAY2[r], B = GRAY2[c]; return (A << 1) | B; } };
    if (nVars === 3) return { rows: GRAY2, cols: GRAY4, rowVars: ['A'], colVars: ['B', 'C'], index({ r, c }) { const A = GRAY2[r], BC = GRAY4[c]; const B = (BC >> 1) & 1, C = BC & 1; return (A << 2) | (B << 1) | C; } };
    if (nVars === 4) return { rows: GRAY4, cols: GRAY4, rowVars: ['A', 'B'], colVars: ['C', 'D'], index({ r, c }) { const AB = GRAY4[r], CD = GRAY4[c]; const A = (AB >> 1) & 1, B = AB & 1, C = (CD >> 1) & 1, D = CD & 1; return (A << 3) | (B << 2) | (C << 1) | D; } };
    return null;
}

// Membuat data Tabel Kebenaran (array of objects)
// Bisa build dari RPN (hasil evaluasi ekspresi)
// ATAU dari mintermSet (hasil impor minterm)
function buildTruthTable(vars, rpn, mintermSet = null) {
    const rows = []; const n = vars.length; const total = 1 << n;
    const useMintermSet = (mintermSet instanceof Set);

    for (let m = 0; m < total; m++) {
        const env = {};
        for (let i = 0; i < n; i++) env[vars[i]] = (m >> (n - 1 - i)) & 1;

        let y;
        if (useMintermSet) {
            // Mode Impor: Y=1 jika 'm' ada di set
            y = mintermSet.has(m) ? 1 : 0;
        } else {
            // Mode Evaluasi: Y = hasil evalRPN
            y = rpn ? evalRPN(rpn, env) : 0;
        }

        rows.push({ m, env, y });
    }
    return rows;
}

/* =======================
 * App State & Wiring
 * ======================= */

// Cache semua elemen DOM penting agar tidak query berulang kali
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
    btnPrintKMap: byId('btn-print-kmap'),
    benchmarkPill: byId('benchmark-pill'), // Benchmark digabung ke panel 3
    themeToggleLabel: byId('theme-toggle-label')
};

// State global aplikasi
let currentKMap = { vars: [], n: 0, layout: null, cells: [], total: 0 };
let currentRPN = null; // RPN terakhir yang dievaluasi

// Mengisi panel statistik di atas
function setPills(vars, minterms, sop, benchmark) {
    els.varsPill.textContent = `${vars.length ? vars.join(', ') : '—'}`;
    els.mintermsPill.textContent = `${minterms.length ? minterms.join(',') : '—'}`;
    els.simpPill.textContent = `${sop || '—'}`;

    // Tampilkan benchmark di panel 'Sederhana'
    els.benchmarkPill.textContent = (benchmark === undefined) ? '—' : `${benchmark.toFixed(2)} ms`;
}

// Render Tabel Kebenaran ke DOM
function renderTruthTable(vars, rows) {
    const thv = vars.map(v => `<th>${v}</th>`).join('');
    els.ttHead.innerHTML = `<tr>${thv}<th>Y</th><th class="muted">m</th></tr>`;
    const bodyHtml = rows.map(r => {
        const vs = vars.map(v => `<td>${r.env[v]}</td>`).join('');
        return `<tr>${vs}<td><b>${r.y}</b></td><td class="muted">${r.m}</td></tr>`;
    }).join('');
    els.ttBody.innerHTML = bodyHtml;
}

// Fungsi utama untuk menggambar K-Map (label + sel)
function initKMap(nVars, varNames) {
    const layout = kmapLayoutForVars(nVars);
    if (!layout) {
        els.kmap.innerHTML = `<div class="muted">Layout K-Map tidak valid.</div>`;
        return;
    }

    // Update state global K-Map
    currentKMap = {
        vars: varNames,
        n: nVars,
        layout: layout,
        cells: new Array(1 << nVars).fill(0), // Reset semua sel ke 0
        total: (1 << nVars)
    };

    // Bersihkan DOM lama
    els.kmapCorner.innerHTML = '';
    els.kmapLabelTop.innerHTML = '';
    els.kmapLabelLeft.innerHTML = '';
    els.kmap.innerHTML = '';

    // Buat label (pojok, atas, kiri)
    const rowLabel = layout.rowVars.join('');
    const colLabel = layout.colVars.join('');
    els.kmapCorner.textContent = `${rowLabel}\\${colLabel}`;

    const colStrings = GRAY_STRINGS[layout.colVars.length] || GRAY_STRINGS[1];
    els.kmapLabelTop.style.gridTemplateColumns = `repeat(${layout.cols.length}, 56px)`;
    for (let c = 0; c < layout.cols.length; c++) {
        const div = document.createElement('div');
        div.className = 'kmap-axis-label';
        div.textContent = colStrings[c];
        els.kmapLabelTop.appendChild(div);
    }

    const rowStrings = GRAY_STRINGS[layout.rowVars.length] || GRAY_STRINGS[1];
     els.kmapLabelLeft.style.gridTemplateRows = `repeat(${layout.rows.length}, 44px)`;
    for (let r = 0; r < layout.rows.length; r++) {
        const div = document.createElement('div');
        div.className = 'kmap-axis-label';
        div.textContent = rowStrings[r];
        els.kmapLabelLeft.appendChild(div);
    }

    // Buat sel K-Map
    // Dibuat sebagai array string lalu .join() agar lebih cepat
    els.kmap.style.gridTemplateColumns = `repeat(${layout.cols.length}, 56px)`;
    const cellsHtml = [];
    for (let r = 0; r < layout.rows.length; r++) {
        for (let c = 0; c < layout.cols.length; c++) {
            const idx = layout.index({ r, c }); // Ambil index minterm dari (r,c)
            cellsHtml.push(
                // Atribut data-index dipakai oleh CSS untuk menampilkan nomor minterm
                `<div class="kcell" data-index="${idx}" title="m${idx}">0</div>`
            );
        }
    }
    els.kmap.innerHTML = cellsHtml.join('');
}

// Fungsi reset UI (dipakai oleh 'Bersihkan')
function setupKMapUI(nVars) {
    const kmapVars = CONTEXT_VARS[nVars];
    initKMap(nVars, kmapVars);

    // Reset semua output
    els.expr.value = '';
    currentRPN = null;
    els.ttHead.innerHTML = '';
    els.ttBody.innerHTML = '';
    els.outSimplified.textContent = '—';
    setPills(kmapVars, [], '—', undefined); // Reset pills
    els.mintermIO.value = '';
    els.errorBox.style.display = 'none';
}

// "Mewarnai" sel K-Map berdasarkan daftar minterm (nilai 1)
function paintKMapFromMinterms(minterms) {
    if (!currentKMap.layout) return;

    const mintermSet = new Set(minterms);
    const children = els.kmap.children;

    for (let k = 0; k < children.length; k++) {
        const cell = children[k];
        const idx = Number(cell.dataset.index);
        const isOne = mintermSet.has(idx);

        // Update state internal & tampilan DOM
        currentKMap.cells[idx] = isOne ? 1 : 0;
        cell.classList.remove('dont-care');
        cell.classList.toggle('on', isOne);
        cell.textContent = isOne ? '1' : '0';
    }
}

// Kumpulan helper untuk mengambil data DARI state K-Map
function collectMintermsFromKMap() {
    const res = [];
    for (let i = 0; i < currentKMap.total; i++)
        if (currentKMap.cells[i] === 1) res.push(i);
    return res.sort((a, b) => a - b);
}
function collectDontCaresFromKMap() {
    const res = [];
    for (let i = 0; i < currentKMap.total; i++)
        if (currentKMap.cells[i] === 2) res.push(i);
    return res.sort((a, b) => a - b);
}
function collectMaxtermsFromKMap() {
    const res = [];
    for (let i = 0; i < currentKMap.total; i++)
        if (currentKMap.cells[i] === 0) res.push(i);
    return res.sort((a, b) => a - b);
}

// Helper untuk konversi implicant F' (dari 0s) ke string POS (Product of Sums)
function implicantsToPOS(impls, vars) {
    if (!impls.length) return '1';
    if (impls.some(mask => mask.split('').every(c => c === '-'))) return '0';

    const parts = impls.map(mask => {
        const literals = [];
        for (let i = 0; i < mask.length; i++) {
            if (mask[i] === '-') continue;
            const v = vars[i];
            // Terapkan De Morgan pada literal
            // SOP F' (1 -> V, 0 -> V') diubah ke POS F (1 -> V', 0 -> V)
            literals.push( (mask[i] === '1') ? (v + "'") : v );
        }
        if (literals.length === 0) return null;
        if (literals.length === 1) return literals[0];
        return `(${literals.join(' + ')})`; // Gabung dengan OR
    }).filter(Boolean);

    return parts.join(''); // Gabung dengan AND implisit
}


// Fungsi utama untuk menjalankan simplifikasi
// Dipanggil oleh tombol "Sederhanakan SOP/POS"
// Mengembalikan objek: { resultString, time }
function simplifyFromKMap(mode = 'SOP') {
    const n = currentKMap.n, vars = currentKMap.vars;
    let resultString;
    let execTime = 0;

    if (n === 0) {
        // Kasus khusus 0-variabel (tidak perlu QM)
        const v = currentKMap.cells[0] || 0;
        resultString = (v === 1) ? '1' : '0';
    } else {
        const dcs = collectDontCaresFromKMap();

        if (mode === 'POS') {
            // ---- Mode POS ----
            // 1. Ambil 0s (Maxterms)
            const maxterms = collectMaxtermsFromKMap();
            // 2. Sederhanakan F' (fungsi dari 0s)
            const { implicants, time } = qmSimplify(maxterms, dcs, vars);
            // 3. Konversi ke string POS
            resultString = implicantsToPOS(implicants, vars);
            execTime = time;
        } else {
            // ---- Mode SOP (default) ----
            // 1. Ambil 1s (Minterms)
            const minterms = collectMintermsFromKMap();
            // 2. Sederhanakan F (fungsi dari 1s)
            const { sop, time } = qmSimplify(minterms, dcs, vars);
            resultString = sop;
            execTime = time;
        }
    }

    els.outSimplified.textContent = resultString;
    return { resultString: resultString, time: execTime };
}

/* =======================
 * Event Listeners (Pengatur Interaksi UI)
 * ======================= */

// Tombol EVALUASI: Alur kerja utama dari Ekspresi
els.btnEval.addEventListener('click', () => {
    try {
        els.errorBox.style.display = 'none';

        // 1. Baca Ekspresi & Deteksi Variabel
        const expr = els.expr.value.trim();
        if (!expr) throw new Error('Masukkan ekspresi.');
        const detectedVars = extractVars(expr);

        // 2. Tentukan Ukuran K-Map (nVars) secara otomatis
        let nVars;
        if (detectedVars.length > 0) {
            if (detectedVars.includes('D')) nVars = 4;
            else if (detectedVars.includes('C')) nVars = 3;
            else nVars = 2; // Default
        } else {
            nVars = currentKMap.n || 3; // Jika tidak ada vars (misal "1+0"), pakai state lama
        }

        // 3. Validasi
        const kmapVars = CONTEXT_VARS[nVars];
        const invalidVars = detectedVars.filter(v => !kmapVars.includes(v));
        if (invalidVars.length > 0) {
            throw new Error(`Variabel '${invalidVars.join(',')}' tidak ada dalam konteks K-Map ${nVars}-variabel.`);
        }

        // 4. Parse & Eval
        const tokens = tokenize(expr);
        currentRPN = toRPN(tokens);
        const rows = buildTruthTable(kmapVars, currentRPN, null); // Mode RPN
        renderTruthTable(kmapVars, rows);

        // 5. Update K-Map
        const minFull = rows.filter(r => r.y === 1).map(r => r.m);
        initKMap(nVars, kmapVars);
        paintKMapFromMinterms(minFull);

        // 6. Sederhanakan (default SOP) & Update UI
        const { resultString: sop, time } = simplifyFromKMap('SOP');
        setPills(kmapVars, minFull, sop, time); // Update pills
        els.mintermIO.value = minFull.join(','); // Update minterm I/O

    } catch (e) {
        console.error("Evaluation Error:", e);
        els.errorBox.textContent = "Kesalahan: " + e.message;
        els.errorBox.style.display = 'block';
    }
});

// Tombol BERSIHKAN: Reset semua
els.btnClear.addEventListener('click', () => {
    // Reset ke 3 variabel sebagai default
    setupKMapUI(3);
});

// BARU: Tekan Enter di Input Ekspresi -> Klik Tombol Evaluasi
els.expr.addEventListener('keydown', (event) => {
    // Periksa apakah tombol yang ditekan adalah Enter
    if (event.key === 'Enter') {
        // Hentikan aksi default Enter (misal: submit form jika ada)
        event.preventDefault();
        // Secara programatik klik tombol Evaluasi
        els.btnEval.click();
    }
});


// Tombol RESET K-MAP: Hanya reset K-Map dan output
els.btnReset.addEventListener('click', () => {
    paintKMapFromMinterms([]);
    els.outSimplified.textContent = '—';
    els.mintermIO.value = '';
    els.expr.value = ''; // Hapus ekspresi juga
    setPills(currentKMap.vars, [], '—', undefined); // Reset pills
});

// Tombol SEDERHANAKAN SOP
els.btnSimplifySOP.addEventListener('click', () => {
    const { resultString: sop, time } = simplifyFromKMap('SOP'); // Panggil mode SOP
    els.expr.value = sop; // Update ekspresi

    // Update panel statistik
    const minterms = collectMintermsFromKMap();
    setPills(currentKMap.vars, minterms, sop, time);
});

// Tombol SEDERHANAKAN POS
els.btnSimplifyPOS.addEventListener('click', () => {
    const { resultString: pos, time } = simplifyFromKMap('POS'); // Panggil mode POS
    els.expr.value = pos; // Update ekspresi

    // Update panel statistik
    const minterms = collectMintermsFromKMap();
    setPills(currentKMap.vars, minterms, pos, time);
});


// Klik pada Sel K-Map (Event Delegation)
els.kmap.addEventListener('click', (e) => {
    const cell = e.target.closest('.kcell');
    if (!cell) return;
    const idx = Number(cell.dataset.index);
    if (isNaN(idx)) return;

    // Siklus nilai sel: 0 -> 1 -> 2(d) -> 0
    const newVal = (currentKMap.cells[idx] + 1) % 3;
    currentKMap.cells[idx] = newVal;

    // Update tampilan
    cell.classList.toggle('on', newVal === 1);
    cell.classList.toggle('dont-care', newVal === 2);
    cell.textContent = (newVal === 2) ? 'd' : String(newVal);
});

// Tombol IMPOR MINTERM: Alur kerja utama dari Minterm
els.btnImport.addEventListener('click', () => {
    try {
        els.errorBox.style.display = 'none';
        const txt = els.mintermIO.value.trim();

        // 1. Parse semua angka
        const parts = txt.split(/[,\s]+/)
            .map(s => s.trim())
            .filter(Boolean)
            .map(Number)
            .filter(n => Number.isInteger(n) && n >= 0);

        // Jika input kosong, reset
        if (!parts.length) {
            const nVars = currentKMap.n || 3;
            const kmapVars = CONTEXT_VARS[nVars];
            paintKMapFromMinterms([]);
            const { resultString: sop, time } = simplifyFromKMap('SOP');
            els.expr.value = sop;
            setPills(kmapVars, [], sop, time);
            const rows = buildTruthTable(kmapVars, null, new Set());
            renderTruthTable(kmapVars, rows);
            return;
        }

        // 2. Tentukan Ukuran K-Map (nVars) secara otomatis
        const maxMinterm = Math.max(...parts);
        let nVars;
        if (maxMinterm < 4) nVars = 2;
        else if (maxMinterm < 8) nVars = 3;
        else if (maxMinterm < 16) nVars = 4;
        else throw new Error(`Minterm '${maxMinterm}' terlalu besar (Maks 15).`);

        const kmapVars = CONTEXT_VARS[nVars];

        // 3. Gambar ulang K-Map jika ukurannya berubah
        if (nVars !== currentKMap.n) {
            initKMap(nVars, kmapVars);
        }

        // 4. Update Tabel Kebenaran (dari MintermSet)
        const finalParts = parts.filter(n => n < (1 << nVars));
        const mintermSet = new Set(finalParts);
        currentRPN = null; // Hapus RPN lama, tidak relevan
        const rows = buildTruthTable(kmapVars, null, mintermSet); // Mode MintermSet
        renderTruthTable(kmapVars, rows);

        // 5. Update K-Map
        paintKMapFromMinterms(finalParts);

        // 6. Sederhanakan (default SOP) & Update UI
        const { resultString: sop, time } = simplifyFromKMap('SOP');
        els.expr.value = sop;
        setPills(kmapVars, finalParts.sort((a,b) => a-b), sop, time);

    } catch (e) {
        console.error("Import Error:", e);
        els.errorBox.textContent = "Kesalahan: " + e.message;
        els.errorBox.style.display = 'block';
    }
});

// Tombol EKSPOR MINTERM
els.btnExport.addEventListener('click', () => {
    // 1. Ambil 1s (minterms) dan 'd's (don't cares)
    const ms = collectMintermsFromKMap();
    const dcs = collectDontCaresFromKMap();

    // 2. Gabungkan & tampilkan di I/O box
    const all = [...new Set([...ms, ...dcs])].sort((a, b) => a - b);
    els.mintermIO.value = all.join(',');

    // 3. Sederhanakan juga (default SOP) agar UI sinkron
    const { resultString: sop, time } = simplifyFromKMap('SOP');
    els.expr.value = sop;
    setPills(currentKMap.vars, ms, sop, time); // Pills hanya tampilkan minterm (1s)
});

// Ganti Toggle Tema
els.themeToggle.addEventListener('change', () => {
    const isLightMode = els.themeToggle.checked;

    // 1. Ganti class di body
    document.body.classList.toggle('light-mode', isLightMode);

    // 2. Teks label tidak perlu diubah karena sudah statis "Mode"
});

// Tombol Cetak/PDF K-Map
els.btnPrintKMap.addEventListener('click', () => {
    window.print(); // Membuka dialog cetak browser
});


// Fungsi untuk memuat contoh ekspresi
const loadExample = (expr) => {
    els.expr.value = expr;
    // Langsung klik Evaluasi (sudah pintar)
    els.btnEval.click();
}
// Pasang listener untuk tombol contoh F1-F10 (BARU)
byId('btn-ex1').addEventListener('click', () => loadExample("A'B + AC")); // F1 (Sama)
byId('btn-ex2').addEventListener('click', () => loadExample("A(B+C)")); // F2 (Sama)
byId('btn-ex3').addEventListener('click', () => loadExample("(A^B)C + A'B'")); // F3 (Sama)
byId('btn-ex4').addEventListener('click', () => loadExample("(A+B)(C+D)")); // F4 (Sama)
byId('btn-ex5').addEventListener('click', () => loadExample("A'B'+AB")); // F5 (XNOR)
byId('btn-ex6').addEventListener('click', () => loadExample("A^B^C")); // F6 (XOR 3 var)
byId('btn-ex7').addEventListener('click', () => loadExample("(A+B'C')(A'+C)")); // F7 (POS style)
byId('btn-ex8').addEventListener('click', () => loadExample("(AB)'+C")); // F8 (NAND + OR)
byId('btn-ex9').addEventListener('click', () => loadExample("AB+AC+BC")); // F9 (Consensus)
byId('btn-ex10').addEventListener('click', () => loadExample("(A+B+C)(A'+B)(B+C')")); // F10 (POS style)


/* =======================
 * Inisialisasi Aplikasi Saat Memuat
 * ======================= */

// Muat ekspresi default saat halaman dibuka
els.btnEval.click();
