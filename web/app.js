/* =======================
 * Utils & Definisi Global
 * ======================= */
// Konstanta nilai Gray Code
const GRAY2 = [0, 1];
const GRAY4 = [0, 1, 3, 2]; // Urutan Gray: 00, 01, 11, 10
// String Gray Code untuk label K-Map
const GRAY_STRINGS = {
    1: ['0', '1'],             // Untuk 1 variabel (misal: A)
    2: ['00', '01', '11', '10'] // Untuk 2 variabel (misal: BC atau CD)
};
// Daftar variabel yang valid berdasarkan pilihan dropdown
const CONTEXT_VARS = {
    2: ['A', 'B'],
    3: ['A', 'B', 'C'],
    4: ['A', 'B', 'C', 'D']
};

// Utility: Get element by ID
const byId = (id) => document.getElementById(id);
// Utility: Konversi desimal ke biner dengan padding nol
const toBin = (n, w) => n.toString(2).padStart(w, '0');

// Utility: Dapatkan variabel unik dari array, urutkan A-Z
function uniqueSortedVars(vars) {
    const set = new Set(vars.map(v => v.toUpperCase()));
    return Array.from(set).sort();
}
// Utility: Ekstrak variabel (A-Z) dari string ekspresi
function extractVars(expr) {
    // Regex untuk mencari huruf A-Z, case-insensitive
    const vars = (expr.match(/[A-Za-z]/g) || []).map(ch => ch.toUpperCase());
    return uniqueSortedVars(vars);
}

/* =======================
 * Tokenizer + Parser (dengan perbaikan implicit AND)
 * ======================= */

// Fungsi Tokenize: Memecah string ekspresi menjadi token (VAR, OP, NUM, LP, RP)
function tokenize(raw) { // Fungsi ini tidak perlu diubah
    const src = raw.replace(/\s+/g, ''); // Hapus spasi
    const tokens = [];
    let i = 0;
    while (i < src.length) {
        let ch = src[i];
        // Angka 0 atau 1
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
        // Kurung buka
        if (ch === '(') { tokens.push({ type: 'LP' }); i++; continue; }
        // Kurung tutup
        if (ch === ')') {
            tokens.push({ type: 'RP' }); i++;
             // Tangani NOT postfix setelah kurung (misal: (A+B)')
            let negCount = 0; while (src[i] === "'") { negCount++; i++; }
            if (negCount % 2 === 1) tokens.push({ type: 'OP', value: 'NOT', unary: true, postfix: true, precedence: 4, associativity: 'right' });
            continue;
        }
        // Operator NOT prefix (! atau ~)
        if (ch === '!' || ch === '~') { tokens.push({ type: 'OP', value: 'NOT', unary: true, prefix: true, precedence: 4, associativity: 'right' }); i++; continue; } // Tandai sebagai prefix
        // Operator AND eksplisit (&, *, .)
        if (ch === '&' || ch === '*' || ch === '.') { tokens.push({ type: 'OP', value: 'AND', precedence: 3, associativity: 'left' }); i++; continue; }
        // Operator OR (+, |)
        if (ch === '+' || ch === '|') { tokens.push({ type: 'OP', value: 'OR', precedence: 1, associativity: 'left' }); i++; continue; }
        // Operator XOR (^)
        if (ch === '^') { tokens.push({ type: 'OP', value: 'XOR', precedence: 2, associativity: 'left' }); i++; continue; }
        // Karakter tidak dikenal
        throw new Error("Karakter tidak dikenali pada posisi " + i + ": '" + ch + "'");
    }
    return tokens;
}

// Helper untuk RPN: Cek apakah token adalah akhir dari sebuah operand
// (Variabel, Angka, NOT postfix, Kurung Tutup)
function endsOperand(tok) {
    return tok && (tok.type === 'VAR' || tok.type === 'NUM' || (tok.type === 'OP' && tok.postfix) || tok.type === 'RP');
}
// Helper untuk RPN: Cek apakah token adalah awal dari sebuah operand
// (Variabel, Angka, Kurung Buka, NOT prefix)
function beginsOperand(tok) {
     // Perbaikan: Ganti t.unary && !t.postfix menjadi t.prefix
     return tok && (tok.type === 'VAR' || tok.type === 'NUM' || tok.type === 'LP' || (tok.type === 'OP' && tok.prefix));
}

// Fungsi toRPN (Shunting Yard): Mengubah infix token menjadi postfix (Reverse Polish Notation)
function toRPN(tokens) {
    const output = []; // Antrian output (hasil RPN)
    const stack = [];  // Tumpukan operator

    // Langkah 1: Sisipkan token AND implisit (LOGIKA DIPERBAIKI)
    const withImplicit = [];
    for (let i = 0; i < tokens.length; i++) {
        withImplicit.push(tokens[i]);
        const a = tokens[i], b = tokens[i + 1];
        // Sisipkan AND jika 'a' adalah akhir operand DAN 'b' adalah awal operand
        if (endsOperand(a) && beginsOperand(b)) {
            withImplicit.push({ type: 'OP', value: 'AND', precedence: 3, associativity: 'left', implicit: true });
        }
    }

    // Langkah 2: Algoritma Shunting Yard
    for (let i = 0; i < withImplicit.length; i++) {
        const t = withImplicit[i];
        // Angka atau Variabel -> langsung ke output
        if (t.type === 'VAR' || t.type === 'NUM') { output.push(t); continue; }
        // Operator NOT postfix -> langsung ke output
        if (t.type === 'OP' && t.postfix && t.value === 'NOT') { output.push(t); continue; }
        // Operator Unary prefix (NOT !) -> ke stack
        // Perbaikan: Ganti t.unary && !t.postfix menjadi t.prefix
        if (t.type === 'OP' && t.prefix && t.value === 'NOT') { stack.push(t); continue; }
        // Operator Biner (AND, OR, XOR)
        if (t.type === 'OP' && !t.unary && !t.postfix && !t.prefix) {
            // Selama ada operator di stack dengan prioritas lebih tinggi/sama (dan left-associative)
            while (stack.length) {
                const top = stack[stack.length - 1];
                // Pastikan top bukan LP dan cek prioritas/asosiativitas
                if (top.type === 'OP' && top.type !== 'LP' && ( (top.precedence > t.precedence) || (top.precedence === t.precedence && t.associativity === 'left') )) {
                     output.push(stack.pop()); // Pindahkan operator dari stack ke output
                } else break; // Berhenti jika prioritas lebih rendah atau right-associative atau LP
            }
            stack.push(t); // Masukkan operator saat ini ke stack
            continue;
        }
        // Kurung buka -> ke stack
        if (t.type === 'LP') { stack.push(t); continue; }
        // Kurung tutup
        if (t.type === 'RP') {
            // Pindahkan operator dari stack ke output sampai ketemu kurung buka
            while (stack.length && stack[stack.length - 1].type !== 'LP') {
                 output.push(stack.pop());
            }
            if (!stack.length || stack[stack.length - 1].type !== 'LP') { // Periksa lagi stack top
                throw new Error("Kurung tidak seimbang (RP tanpa LP)"); // Error jika tidak ketemu LP
            }
            stack.pop(); // Buang kurung buka (LP) dari stack
            continue;
        }
    }
    // Setelah semua token diproses, pindahkan sisa operator di stack ke output
    while (stack.length) {
        const s = stack.pop();
        if (s.type === 'LP') throw new Error("Kurung tidak seimbang (sisa LP)"); // Error jika masih ada LP
        output.push(s);
    }
    return output;
}

// Fungsi evalRPN: Mengevaluasi ekspresi RPN dengan nilai variabel dari 'env'
function evalRPN(rpn, env) {
    const st = []; // Stack untuk menyimpan nilai sementara
    for (const t of rpn) {
        // Angka -> push nilainya (boolean) ke stack
        if (t.type === 'NUM') st.push(!!t.value);
        // Variabel -> push nilainya dari 'env' (boolean) ke stack
        else if (t.type === 'VAR') {
            // Cek dulu apakah variabel ada di env
            if (!(t.value in env)) {
                 // Jika tidak ada, anggap 0 (false), ini menangani kasus misal ekspresi 'A' di konteks ['A','B']
                 st.push(false);
                 // Atau bisa lempar error: throw new Error(`Variabel ${t.value} tidak didefinisikan dalam konteks`);
            } else {
                 st.push(!!env[t.value]);
            }
        }
        // Operator
        else if (t.type === 'OP') {
            // Operator NOT (unary, bisa prefix atau postfix)
            if (t.value === 'NOT') {
                if (st.length < 1) throw new Error("Operator NOT kekurangan operand");
                const a = st.pop(); st.push(!a); // Ambil 1 nilai, operasikan, push hasil
            }
            // Operator Biner (AND, OR, XOR)
            else {
                if (st.length < 2) throw new Error(`Operator ${t.value} kekurangan operand`);
                const b = st.pop(); const a = st.pop(); // Ambil 2 nilai
                // Lakukan operasi sesuai jenis operator
                if (t.value === 'AND') st.push(a && b);
                else if (t.value === 'OR') st.push(a || b);
                else if (t.value === 'XOR') st.push(Boolean(a) !== Boolean(b)); // XOR boolean
                else throw new Error("Operator tidak dikenal: " + t.value);
                // Push hasil operasi ke stack
            }
        }
    }
    // Setelah semua token diproses, harusnya hanya ada 1 nilai di stack (hasil akhir)
    if (st.length !== 1) throw new Error("Ekspresi tidak valid (hasil akhir stack != 1)");
    return st[0] ? 1 : 0; // Kembalikan hasil (1 atau 0)
}


/* =======================
 * Quine–McCluskey (SOP) (Algoritma simplifikasi, tidak perlu komentar detail di sini)
 * ======================= */
function countOnes(binStr) { return binStr.split('').filter(c => c === '1').length; }
function canCombine(a, b) { let diff = 0; for (let i = 0; i < a.length; i++) { if (a[i] !== b[i]) diff++; if (diff > 1) return false; } return diff === 1; }
function combine(a, b) { let r = ''; for (let i = 0; i < a.length; i++) { r += (a[i] === b[i]) ? a[i] : '-'; } return r; }
function covers(imp, mintermBin) { for (let i = 0; i < imp.length; i++) { if (imp[i] === '-') continue; if (imp[i] !== mintermBin[i]) return false; } return true; }
function qmSimplify(minterms, dontcares, varNames) {
    dontcares = dontcares || [];
    if (!minterms.length && !dontcares.length) return { implicants: [], sop: '0' };
    if (!minterms.length) return { implicants: [], sop: '0' };
    const W = varNames.length;
    const minBins = minterms.map(m => toBin(m, W));
    const dcBins = dontcares.map(m => toBin(m, W));
    const allBins = [...new Set([...minBins, ...dcBins])];
    if (allBins.length === (1 << W) && dcBins.length < allBins.length) return { implicants: ['-'.repeat(W)], sop: '1' };
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
        if (bestJ === -1) { // Jika tidak ada lagi yg bisa dipilih tapi belum semua tercover
             // Ini bisa terjadi jika ada minterm yg hanya dicover oleh implicant non-esensial yg redundan
             // Kita bisa break saja atau implementasi algoritma Petrick's method
             // Untuk sekarang, break sudah cukup
             break;
        }
        chosen.add(bestJ); markCovered();
    }
    const implicants = Array.from(chosen).map(j => primeList[j]);
    const sop = implicantsToSOP(implicants, varNames);
    return { implicants, sop };
}

function implicantsToSOP(impls, vars) {
    if (!impls.length) return '0';
    if (impls.some(mask => mask.split('').every(c => c === '-'))) return '1';
    const parts = impls.map(mask => {
        let s = ''; for (let i = 0; i < mask.length; i++) { if (mask[i] === '-') continue; const v = vars[i]; s += (mask[i] === '1') ? v : (v + "'"); } return s;
    }).filter(Boolean); // Filter string kosong jika ada (meski seharusnya tidak)
    return parts.join(' + ');
}


/* =======================
 * K-Map Logic & Rendering (dengan perbaikan loop)
 * ======================= */

// Fungsi get K-Map layout (jumlah baris/kolom, variabel axis, fungsi mapping index)
function kmapLayoutForVars(nVars) { // tidak berubah
    if (nVars === 1) return { rows: GRAY2, cols: [0], rowVars: ['A'], colVars: [], index(rc) { return GRAY2[rc.r]; } };
    if (nVars === 2) return { rows: GRAY2, cols: GRAY2, rowVars: ['A'], colVars: ['B'], index({ r, c }) { const A = GRAY2[r], B = GRAY2[c]; return (A << 1) | B; } };
    if (nVars === 3) return { rows: GRAY2, cols: GRAY4, rowVars: ['A'], colVars: ['B', 'C'], index({ r, c }) { const A = GRAY2[r], BC = GRAY4[c]; const B = (BC >> 1) & 1, C = BC & 1; return (A << 2) | (B << 1) | C; } };
    if (nVars === 4) return { rows: GRAY4, cols: GRAY4, rowVars: ['A', 'B'], colVars: ['C', 'D'], index({ r, c }) { const AB = GRAY4[r], CD = GRAY4[c]; const A = (AB >> 1) & 1, B = AB & 1, C = (CD >> 1) & 1, D = CD & 1; return (A << 3) | (B << 2) | (C << 1) | D; } };
    return null; // Tidak valid jika bukan 1-4
}

// Fungsi membuat data Tabel Kebenaran
function buildTruthTable(vars, rpn) { // tidak berubah
    const rows = []; const n = vars.length; const total = 1 << n; // 2^n baris
    // Loop untuk setiap minterm (0 sampai 2^n - 1)
    for (let m = 0; m < total; m++) {
        const env = {}; // Environment (nilai variabel A, B, C, ...)
        // Set nilai variabel A, B, C... berdasarkan bit dari minterm 'm'
        for (let i = 0; i < n; i++) env[vars[i]] = (m >> (n - 1 - i)) & 1;
        // Evaluasi ekspresi RPN dengan environment saat ini
        const y = rpn ? evalRPN(rpn, env) : 0; // Hasil Y (0 atau 1)
        rows.push({ m, env, y }); // Simpan data baris
    }
    return rows;
}

/* =======================
 * App State & Wiring
 * ======================= */

// Cache referensi ke elemen DOM penting
const els = {
    expr: byId('expr'),
    kmapVarSelect: byId('kmap-vars'),     // Dropdown Pilih Ukuran
    btnEval: byId('btn-eval'),           // Tombol Evaluasi
    btnClear: byId('btn-clear'),         // Tombol Bersihkan
    varsPill: byId('vars-pill'),     // Panel stat: Variabel
    mintermsPill: byId('minterms-pill'), // Panel stat: Minterm
    simpPill: byId('simp-pill'),     // Panel stat: Sederhana (SOP)
    ttHead: byId('ttbl').querySelector('thead'), // Header tabel kebenaran
    ttBody: byId('ttbl').querySelector('tbody'), // Body tabel kebenaran
    kmapContainer: byId('kmap-container'),   // Kontainer K-Map (grid)
    kmapCorner: byId('kmap-corner'),       // Pojok K-Map
    kmapLabelTop: byId('kmap-label-top'),    // Label atas K-Map
    kmapLabelLeft: byId('kmap-label-left'),   // Label kiri K-Map
    kmap: byId('kmap'),                      // Grid sel K-Map
    btnSimplify: byId('btn-simplify'),       // Tombol Sederhanakan
    btnReset: byId('btn-reset'),         // Tombol Reset K-Map
    outSimplified: byId('out-simplified'),   // Output SOP
    mintermIO: byId('minterm-io'),         // Input/Output minterm
    btnImport: byId('btn-import'),       // Tombol Impor
    btnExport: byId('btn-export'),       // Tombol Ekspor
    errorBox: byId('error-box'),           // Kotak pesan error
    themeToggle: byId('theme-toggle-cb'),    // Checkbox ganti tema
};

// State global aplikasi
let currentKMap = { vars: [], n: 0, layout: null, cells: [], total: 0 }; // Info K-Map saat ini
let currentRPN = null; // Hasil RPN dari ekspresi terakhir yang dievaluasi

// Fungsi untuk update teks di panel statistik
function setPills(vars, minterms, sop) {
    els.varsPill.textContent = `${vars.length ? vars.join(', ') : '—'}`;
    els.mintermsPill.textContent = `${minterms.length ? minterms.join(',') : '—'}`;
    els.simpPill.textContent = `${sop || '—'}`;
}

// Fungsi untuk me-render Tabel Kebenaran ke DOM
function renderTruthTable(vars, rows) {
    // Buat header tabel (A, B, C, ..., Y, m)
    const thv = vars.map(v => `<th>${v}</th>`).join('');
    els.ttHead.innerHTML = `<tr>${thv}<th>Y</th><th class="muted">m</th></tr>`;
    // Buat baris-baris data tabel
    const bodyHtml = rows.map(r => {
        const vs = vars.map(v => `<td>${r.env[v]}</td>`).join(''); // Nilai A, B, C...
        return `<tr>${vs}<td><b>${r.y}</b></td><td class="muted">${r.m}</td></tr>`; // Baris lengkap
    }).join('');
    els.ttBody.innerHTML = bodyHtml; // Set HTML body tabel
}

// Fungsi untuk menginisialisasi/menggambar ulang K-Map (label + sel)
function initKMap(nVars, varNames) { // Fungsi ini sudah benar
    const layout = kmapLayoutForVars(nVars); // Dapatkan layout K-Map
    if (!layout) { // Jika layout tidak valid (misal nVars = 0)
        els.kmap.innerHTML = `<div class="muted">Layout K-Map tidak valid.</div>`;
        return;
    }

    // Update state K-Map global
    currentKMap = {
        vars: varNames, // Nama variabel (['A', 'B', 'C'])
        n: nVars,       // Jumlah variabel (3)
        layout: layout,   // Objek layout dari kmapLayoutForVars
        cells: new Array(1 << nVars).fill(0), // Array nilai sel (reset ke 0 semua)
        total: (1 << nVars) // Jumlah total sel (8)
    };

    // Bersihkan elemen K-Map lama
    els.kmapCorner.innerHTML = '';
    els.kmapLabelTop.innerHTML = '';
    els.kmapLabelLeft.innerHTML = '';
    els.kmap.innerHTML = '';

    // Buat label pojok (misal: A\BC atau AB\CD)
    const rowLabel = layout.rowVars.join('');
    const colLabel = layout.colVars.join('');
    els.kmapCorner.textContent = `${rowLabel}\\${colLabel}`;

    // Buat label atas (kolom) berdasarkan Gray code
    const colStrings = GRAY_STRINGS[layout.colVars.length] || GRAY_STRINGS[1];
    els.kmapLabelTop.style.gridTemplateColumns = `repeat(${layout.cols.length}, 56px)`;
    for (let c = 0; c < layout.cols.length; c++) {
        const div = document.createElement('div');
        div.className = 'kmap-axis-label';
        div.textContent = colStrings[c];
        els.kmapLabelTop.appendChild(div);
    }

    // Buat label kiri (baris) berdasarkan Gray code
    const rowStrings = GRAY_STRINGS[layout.rowVars.length] || GRAY_STRINGS[1];
     els.kmapLabelLeft.style.gridTemplateRows = `repeat(${layout.rows.length}, 44px)`;
    for (let r = 0; r < layout.rows.length; r++) {
        const div = document.createElement('div');
        div.className = 'kmap-axis-label';
        div.textContent = rowStrings[r];
        els.kmapLabelLeft.appendChild(div);
    }

    // Buat sel-sel K-Map (bagian grid utama)
    els.kmap.style.gridTemplateColumns = `repeat(${layout.cols.length}, 56px)`;
    const cellsHtml = []; // Gunakan array string untuk performa
    for (let r = 0; r < layout.rows.length; r++) {
        for (let c = 0; c < layout.cols.length; c++) {
            const idx = layout.index({ r, c }); // Dapatkan index minterm dari posisi (r, c)
            cellsHtml.push(
                // Buat HTML string untuk sel
                `<div class="kcell" data-index="${idx}" title="m${idx}">0</div>`
            );
        }
    }
    els.kmap.innerHTML = cellsHtml.join(''); // Set HTML grid K-Map sekali jalan
}

// Fungsi untuk setup UI K-Map saat dropdown berubah (tanpa evaluasi ekspresi)
function setupKMapUI(nVars) {
    const kmapVars = CONTEXT_VARS[nVars]; // Dapatkan nama variabel sesuai nVars
    initKMap(nVars, kmapVars); // Gambar ulang K-Map
    // Reset semua output dan input ekspresi
    els.expr.value = '';
    currentRPN = null;
    els.ttHead.innerHTML = '';
    els.ttBody.innerHTML = '';
    els.outSimplified.textContent = '—';
    setPills(kmapVars, [], '—'); // Reset panel stat (hanya tampilkan variabel konteks)
    els.mintermIO.value = '';
    els.errorBox.style.display = 'none'; // Sembunyikan pesan error
}

// Fungsi untuk mewarnai sel K-Map berdasarkan array minterm (hanya nilai 1)
function paintKMapFromMinterms(minterms) {
    if (!currentKMap.layout) return; // Jangan lakukan apa-apa jika K-Map belum siap

    const mintermSet = new Set(minterms); // Gunakan Set untuk pencarian cepat O(1)
    const children = els.kmap.children; // Ambil semua elemen sel K-Map

    // Loop melalui setiap sel di DOM
    for (let k = 0; k < children.length; k++) {
        const cell = children[k];
        const idx = Number(cell.dataset.index); // Ambil index minterm dari data-* attribute

        const isOne = mintermSet.has(idx); // Cek apakah index ini ada di daftar minterm
        currentKMap.cells[idx] = isOne ? 1 : 0; // Update state internal (0 atau 1)

        // Update tampilan DOM sel
        cell.classList.remove('dont-care'); // Hapus class 'dont-care' (karena impor hanya 1)
        cell.classList.toggle('on', isOne); // Tambah/hapus class 'on'
        cell.textContent = isOne ? '1' : '0'; // Set teks (0 atau 1)
    }
}

// Fungsi untuk mengumpulkan minterm (nilai 1) dari state K-Map saat ini
function collectMintermsFromKMap() {
    const res = [];
    for (let i = 0; i < currentKMap.total; i++)
        if (currentKMap.cells[i] === 1) res.push(i);
    return res.sort((a, b) => a - b); // Urutkan
}
// Fungsi untuk mengumpulkan don't care (nilai 2) dari state K-Map saat ini
function collectDontCaresFromKMap() {
    const res = [];
    for (let i = 0; i < currentKMap.total; i++)
        if (currentKMap.cells[i] === 2) res.push(i);
    return res.sort((a, b) => a - b); // Urutkan
}

// Fungsi untuk menjalankan simplifikasi berdasarkan state K-Map saat ini
function simplifyFromKMap() {
    const n = currentKMap.n, vars = currentKMap.vars; // Ambil info dari state
    if (n === 0) { // Kasus khusus jika tidak ada variabel
        const v = currentKMap.cells[0] || 0;
        els.outSimplified.textContent = (v === 1) ? '1' : '0';
        return;
    }
    const ms = collectMintermsFromKMap(); // Kumpulkan minterm (1)
    const dcs = collectDontCaresFromKMap(); // Kumpulkan don't care (d)
    // Jalankan algoritma Quine-McCluskey
    const { sop } = qmSimplify(ms, dcs, vars);
    els.outSimplified.textContent = sop; // Tampilkan hasil SOP
}

/* =======================
 * Event Listeners (Pengatur Interaksi UI)
 * ======================= */

// Klik Tombol Evaluasi
els.btnEval.addEventListener('click', () => {
    try {
        els.errorBox.style.display = 'none'; // Sembunyikan error lama

        // 1. Dapatkan Konteks Variabel dari Dropdown
        const nVars = parseInt(els.kmapVarSelect.value, 10);
        const kmapVars = CONTEXT_VARS[nVars]; // misal: ['A', 'B', 'C']

        // 2. Baca & Validasi Ekspresi
        const expr = els.expr.value.trim();
        if (!expr) throw new Error('Masukkan ekspresi.');
        const detectedVars = extractVars(expr); // Variabel yang ada di ekspresi
        // Cek apakah ada variabel di ekspresi yang TIDAK ADA di konteks
        const invalidVars = detectedVars.filter(v => !kmapVars.includes(v));
        if (invalidVars.length > 0) {
            throw new Error(`Variabel '${invalidVars.join(',')}' tidak ada dalam konteks K-Map ${nVars}-variabel (${kmapVars.join(',')}).`);
        }

        // 3. Proses Ekspresi -> RPN -> Tabel Kebenaran
        const tokens = tokenize(expr);
        console.log("Tokens:", JSON.stringify(tokens)); // Debug: Tampilkan token
        currentRPN = toRPN(tokens); // Simpan RPN untuk evaluasi
        console.log("RPN:", JSON.stringify(currentRPN)); // Debug: Tampilkan RPN
        // Buat tabel kebenaran LENGKAP sesuai konteks (kmapVars)
        const rows = buildTruthTable(kmapVars, currentRPN);
        renderTruthTable(kmapVars, rows); // Tampilkan tabel ke DOM

        // 4. Hitung Minterm & Update K-Map
        const minFull = rows.filter(r => r.y === 1).map(r => r.m); // Dapatkan array minterm (hasil Y=1)
        console.log("Minterms:", minFull); // Debug: Tampilkan minterm
        initKMap(nVars, kmapVars);       // Reset & gambar ulang K-Map sesuai konteks
        paintKMapFromMinterms(minFull); // Warnai sel K-Map sesuai minterm

        // 5. Sederhanakan & Tampilkan Hasil
        const { sop } = qmSimplify(minFull, [], kmapVars); // Sederhanakan (tanpa don't care awal)
        console.log("SOP Result:", sop); // Debug: Tampilkan hasil SOP
        els.outSimplified.textContent = sop; // Tampilkan SOP

        // 6. Update Panel Statistik
        setPills(kmapVars, minFull, sop);

    } catch (e) { // Tangani jika ada error saat proses
        console.error("Evaluation Error:", e); // Log error ke console (untuk debug)
        els.errorBox.textContent = "Kesalahan: " + e.message; // Tampilkan pesan error di UI
        els.errorBox.style.display = 'block';
    }
});

// Klik Tombol Bersihkan
els.btnClear.addEventListener('click', () => {
    // Reset UI K-Map sesuai ukuran yang dipilih di dropdown
    const nVars = parseInt(els.kmapVarSelect.value, 10);
    setupKMapUI(nVars);
});

// Ganti Pilihan Dropdown Ukuran K-Map
els.kmapVarSelect.addEventListener('change', () => {
     // Reset UI K-Map sesuai ukuran BARU yang dipilih
     const nVars = parseInt(els.kmapVarSelect.value, 10);
     setupKMapUI(nVars);
});

// Klik Tombol Reset K-Map
els.btnReset.addEventListener('click', () => {
    paintKMapFromMinterms([]); // Reset semua sel K-Map ke 0
    els.outSimplified.textContent = '—'; // Reset output SOP
});

// Klik Tombol Sederhanakan (SOP)
els.btnSimplify.addEventListener('click', () => {
    simplifyFromKMap(); // Jalankan simplifikasi berdasarkan K-Map saat ini
});

// Klik pada Sel K-Map (Event Delegation)
els.kmap.addEventListener('click', (e) => {
    const cell = e.target.closest('.kcell'); // Cari elemen .kcell terdekat yang diklik
    if (!cell) return; // Abaikan jika klik di luar sel
    const idx = Number(cell.dataset.index); // Ambil index minterm sel
    if (isNaN(idx)) return; // Abaikan jika index tidak valid

    // Siklus nilai sel: 0 -> 1 -> 2(d) -> 0
    const newVal = (currentKMap.cells[idx] + 1) % 3;
    currentKMap.cells[idx] = newVal; // Update state internal

    // Update tampilan DOM sel
    cell.classList.toggle('on', newVal === 1);
    cell.classList.toggle('dont-care', newVal === 2);
    cell.textContent = (newVal === 2) ? 'd' : String(newVal);
});

// Klik Tombol Impor Minterm
els.btnImport.addEventListener('click', () => {
    const txt = els.mintermIO.value.trim(); // Ambil teks dari input
    if (!txt) { // Jika kosong, reset K-Map
        paintKMapFromMinterms([]);
        els.outSimplified.textContent = '—';
        return;
    }
    // Parse teks input (pisahkan dengan koma/spasi, ubah ke angka, filter yang valid)
    const parts = txt.split(/[,\s]+/)
        .map(s => s.trim())
        .filter(Boolean)
        .map(Number)
        .filter(n => Number.isInteger(n) && n >= 0 && n < currentKMap.total);

    paintKMapFromMinterms(parts); // Warnai K-Map (hanya nilai 1)
    simplifyFromKMap(); // Langsung sederhanakan (hanya berdasarkan nilai 1)
});

// Klik Tombol Ekspor Minterm
els.btnExport.addEventListener('click', () => {
    const ms = collectMintermsFromKMap(); // Kumpulkan minterm (1)
    const dcs = collectDontCaresFromKMap(); // Kumpulkan don't care (d)
    // Gabungkan keduanya, hapus duplikat, urutkan
    const all = [...new Set([...ms, ...dcs])].sort((a, b) => a - b);
    els.mintermIO.value = all.join(','); // Tampilkan di input
});

// Ganti Toggle Tema
els.themeToggle.addEventListener('change', () => {
    // Tambah/hapus class 'light-mode' pada body
    document.body.classList.toggle('light-mode', els.themeToggle.checked);
});

// Fungsi untuk memuat contoh ekspresi
const loadExample = (expr) => {
    els.expr.value = expr; // Set input ekspresi
    // Deteksi variabel tertinggi untuk menentukan ukuran K-Map default
    const vars = extractVars(expr);
    if (vars.includes('D')) {
        els.kmapVarSelect.value = '4';
    } else if (vars.includes('C')) {
        els.kmapVarSelect.value = '3';
    } else {
        els.kmapVarSelect.value = '2';
    }
    els.btnEval.click(); // Jalankan evaluasi
}
// Pasang listener untuk tombol contoh F1-F5
byId('btn-ex1').addEventListener('click', () => loadExample("A'B + AC"));
byId('btn-ex2').addEventListener('click', () => loadExample("A(B+C)"));
byId('btn-ex3').addEventListener('click', () => loadExample("(A^B)C + A'B'"));
byId('btn-ex4').addEventListener('click', () => loadExample("(A+B)(C+D)"));
byId('btn-ex5').addEventListener('click', () => loadExample("A'B' + AB"));

/* =======================
 * Inisialisasi Aplikasi Saat Memuat
 * ======================= */
// Set dropdown ke 3 variabel sebagai default
els.kmapVarSelect.value = '3';
// Jalankan evaluasi untuk ekspresi default ("A'B + AC")
els.btnEval.click();