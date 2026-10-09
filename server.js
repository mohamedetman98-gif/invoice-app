'use strict';
const _v = process.versions.node.split('.').map(Number);
if (_v[0] < 22 || (_v[0] === 22 && _v[1] < 5)) { console.error('يلزم Node.js إصدار 22.5 أو أحدث. الإصدار الحالي: ' + process.versions.node); process.exit(1); }
/* =====================================================================
   خادم نظام أذون الفواتير — بدون أي مكتبات خارجية (Node.js 22.5+ فقط)
   قاعدة بيانات SQLite مدمجة + تحديث لحظي عبر SSE + صلاحيات على الخادم
   فكرة وتنفيذ: محمد صبري (نسخة مصححة ومؤمنة)
   ===================================================================== */
const http = require('node:http'), fs = require('node:fs'), path = require('node:path'), crypto = require('node:crypto'), zlib = require('node:zlib');
const { DatabaseSync } = require('node:sqlite');

const PORT = +process.env.PORT || 3000, HOST = process.env.HOST || '0.0.0.0';
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(__dirname, 'data'));
const PUBLIC = path.join(__dirname, 'public');
const SESSION_MS = (+process.env.SESSION_DAYS || 14) * 864e5;
const MAX_BODY = 80 * 1024 * 1024;
fs.mkdirSync(path.join(DATA_DIR, 'backups'), { recursive: true });

/* ---------------- قاعدة البيانات ---------------- */
const db = new DatabaseSync(path.join(DATA_DIR, 'invoices.db'));
db.exec(`PRAGMA journal_mode=WAL; PRAGMA synchronous=NORMAL;
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT UNIQUE NOT NULL COLLATE NOCASE, salt TEXT, hash TEXT, role TEXT NOT NULL, active INTEGER NOT NULL DEFAULT 1, pm TEXT, must_change INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS sessions(token TEXT PRIMARY KEY, user_id INTEGER NOT NULL, created INTEGER, last INTEGER);
CREATE TABLE IF NOT EXISTS invoices(id TEXT PRIMARY KEY, data TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS kv(k TEXT PRIMARY KEY, v TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS backups(at TEXT PRIMARY KEY, label TEXT, by TEXT, n INTEGER, u INTEGER, blob BLOB);`);
const Q = s => db.prepare(s);
function tx(fn) { db.exec('BEGIN IMMEDIATE'); try { const r = fn(); db.exec('COMMIT'); return r; } catch (e) { try { db.exec('ROLLBACK'); } catch (_) {} throw e; } }
const kvGet = (k, d) => { const r = Q('SELECT v FROM kv WHERE k=?').get(k); return r ? JSON.parse(r.v) : d; };
const kvSet = (k, v) => Q('INSERT INTO kv(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v').run(k, JSON.stringify(v));

/* ---------------- ثوابت ومنطق الأعمال (نفس قواعد الواجهة) ---------------- */
const ST = ['Not Received', 'Received', 'Returned', 'Partial'], PAY = ['Unpaid', 'Paid'];
const ERP_FIELDS = ['Invoice_Date', 'Customer_Code', 'Customer_Name', 'Address', 'Transaction_Type', 'Category1', 'Sales_Order', 'Driver_Name', 'Amount', 'Payment_Term', 'Customer_Category', 'Warehouse', 'Driver_Location', 'Registration'];
const EDITABLE = ['Status', 'Paid_Status', 'PO_Number', 'Return_Number', 'Notes'];
const MASTER_FIELDS = [...ERP_FIELDS.filter(k => k !== 'Driver_Location'), ...EDITABLE];
const PERMS = ['edit', 'import', 'export', 'replace', 'lookups', 'backup', 'restore'];
const ROLE_DEF = { admin: Object.fromEntries(PERMS.map(k => [k, true])), entry: { edit: true, import: true, export: true }, viewer: {} };
const ROLES = Object.keys(ROLE_DEF);
class HttpError extends Error { constructor(s, m, extra) { super(m); this.status = s; this.extra = extra; } }
const bad = m => new HttpError(400, m);
function can(u, p) { if (!u) return false; if (u.role === 'admin') return true; const o = u.pm ? u.pm[p] : undefined; return o !== undefined ? !!o : !!(ROLE_DEF[u.role] || {})[p]; }
function need(u, p) { if (!can(u, p)) throw new HttpError(403, 'ليست لديك صلاحية هذه العملية'); }
const cz = x => { if (x == null) return ''; const t = String(x).trim(); return /^0+(\.0+)?$/.test(t) ? '' : t.slice(0, 200); };
function sanitize(k, v) {
  if (k === 'Amount') { if (v === '' || v == null) return ''; const n = Number(v); return isNaN(n) ? '' : n; }
  if (k === 'Invoice_Date') { const t = String(v == null ? '' : v).trim(); return /^\d{4}-\d{2}-\d{2}$/.test(t) ? t : t.slice(0, 40); }
  return String(v == null ? '' : v).trim().slice(0, 500);
}

/* ---------------- الفواتير: ذاكرة + قاعدة ---------------- */
const INV = new Map();
for (const r of Q('SELECT id,data FROM invoices').all()) INV.set(r.id, JSON.parse(r.data));
const putInv = o => Q('INSERT INTO invoices(id,data) VALUES(?,?) ON CONFLICT(id) DO UPDATE SET data=excluded.data').run(o.Invoice_ID, JSON.stringify(o));
function newInv(id, f) {
  const o = { Invoice_ID: id, Status: 'Not Received', Paid_Status: 'Unpaid', Notes: '', Return_Number: '', PO_Number: '', First_Editor: '', First_At: 0, User_Name: '', ts: 0, Received_At: 0 };
  for (const k of ERP_FIELDS) if (k in f) o[k] = sanitize(k, f[k]);
  return o;
}
/* تطبيق الحقول القابلة للتعديل مع ختم المستخدم والوقت من الخادم */
function applyFields(inv, fields, now, user) {
  let ch = false;
  for (const k of EDITABLE) {
    if (!(k in fields)) continue; let v = fields[k];
    if (k === 'Status') { if (!ST.includes(v)) throw bad('حالة استلام غير صالحة'); if (inv.Status !== v) { if (v === 'Received') inv.Received_At = now; else if (inv.Status === 'Received') inv.Received_At = 0; inv.Status = v; ch = true; } }
    else if (k === 'Paid_Status') { if (!PAY.includes(v)) throw bad('حالة دفع غير صالحة'); if ((inv.Paid_Status || 'Unpaid') !== v) { inv.Paid_Status = v; ch = true; } }
    else { v = (k === 'Notes') ? String(v == null ? '' : v).trim().slice(0, 4000) : cz(v); if ((inv[k] || '') !== v) { inv[k] = v; ch = true; } }
  }
  if (ch) { inv.First_Editor = inv.First_Editor || user.u; inv.First_At = inv.First_At || now; inv.User_Name = user.u; inv.ts = now; }
  return ch;
}

/* ---------------- المستخدمون والجلسات ---------------- */
const hashPw = (pw, salt) => new Promise((res, rej) => crypto.pbkdf2(pw, salt, 100000, 32, 'sha256', (e, k) => e ? rej(e) : res(k.toString('hex'))));
const newSalt = () => crypto.randomBytes(16).toString('hex');
const safeEq = (a, b) => { const x = Buffer.from(a), y = Buffer.from(b); return x.length === y.length && crypto.timingSafeEqual(x, y); };
const pub = r => { const o = { u: r.username, role: r.role, active: !!r.active }; const pm = r.pm ? JSON.parse(r.pm) : null; if (pm && Object.keys(pm).length) o.pm = pm; if (r.must_change) o.mustChange = true; return o; };
async function addUser(username, password, role, mustChange) {
  if (!ROLES.includes(role)) throw bad('دور غير صالح'); username = String(username || '').trim();
  if (!/^[\w.\-@\u0600-\u06FF ]{2,40}$/.test(username)) throw bad('اسم المستخدم غير صالح (حروف وأرقام ونقطة وشرطة، من 2 إلى 40)');
  if (String(password || '').length < 6) throw bad('كلمة المرور 6 أحرف على الأقل');
  if (Q('SELECT 1 FROM users WHERE username=?').get(username)) throw bad('اسم المستخدم موجود بالفعل');
  const salt = newSalt(), hash = await hashPw(password, salt);
  Q('INSERT INTO users(username,salt,hash,role,active,must_change) VALUES(?,?,?,?,1,?)').run(username, salt, hash, role, mustChange ? 1 : 0);
}
(async () => {
  if (!Q('SELECT COUNT(*) c FROM users').get().c) {
    const pw = process.env.ADMIN_PASSWORD || crypto.randomBytes(6).toString('base64url');
    await addUser('admin', pw, 'admin', true);
    console.log('\n==============================================================\n  تم إنشاء حساب المدير لأول مرة:\n  اسم المستخدم: admin\n  كلمة المرور المؤقتة: ' + pw + '\n  (سيُطلب منك تغييرها عند أول دخول — سجّلها الآن فلن تظهر مرة أخرى)\n==============================================================\n');
  }
})();
const parseCookie = req => Object.fromEntries((req.headers.cookie || '').split(';').map(s => s.trim().split('=')).filter(a => a[0]).map(a => [a[0], decodeURIComponent(a.slice(1).join('='))]));

function sessionOf(req) {
  const t = parseCookie(req).sid; if (!t) return null;
  const s = Q('SELECT s.token tok, s.last last, u.* FROM sessions s JOIN users u ON u.id=s.user_id WHERE s.token=?').get(t); if (!s) return null;
  const now = Date.now(); 
  if (!s.active || now - s.last > SESSION_MS) { Q('DELETE FROM sessions WHERE token=?').run(t); return null; }
  if (now - s.last > 300000) Q('UPDATE sessions SET last=? WHERE token=?').run(now, t);
  
  let parsedPm = null;
  if (s.pm) {
    try { parsedPm = JSON.parse(s.pm); } catch (_) { parsedPm = null; }
  }
  return { token: t, id: s.id, u: s.username, role: s.role, pm: parsedPm, mustChange: !!s.must_change };
}

const fails = new Map();
function throttle(key) { const f = fails.get(key); if (f && f.n >= 8 && Date.now() - f.t < 300000) throw new HttpError(423, 'محاولات دخول كثيرة. حاول بعد 5 دقائق'); }
const failed = key => { const f = fails.get(key) || { n: 0, t: 0 }; f.n = Date.now() - f.t > 300000 ? 1 : f.n + 1; f.t = Date.now(); fails.set(key, f); };

/* ---------------- التحديث اللحظي (SSE) ---------------- */
const clients = new Set();
function broadcast(type, data, filter) {
  const msg = 'event: ' + type + '\ndata: ' + JSON.stringify(data) + '\n\n';
  for (const c of clients) { if (filter && !filter(c)) continue; try { c.res.write(msg); } catch (_) { clients.delete(c); } }
}
setInterval(() => { for (const c of clients) { try { c.res.write(': ping\n\n'); } catch (_) { clients.delete(c); } } }, 20000).unref();
function dropClients(pred) { for (const c of [...clients]) if (pred(c)) { try { c.res.end(); } catch (_) {} clients.delete(c); } }

/* ---------------- النسخ الاحتياطي ---------------- */
const bkSettings = () => ({ autoFile: true, hours: 24, fileHours: 24, keep: 30, keepFiles: 30, lastSnap: null, lastFile: null, ...kvGet('bkset', {}) });
function snapshot() { return { app: 'invoice-server', v: 3, at: new Date().toISOString(), users: Q('SELECT username,salt,hash,role,active,pm,must_change FROM users').all(), invs: [...INV.values()], WH: kvGet('WH', []), DR: kvGet('DR', []) }; }
function saveBackup(label, by) {
  const d = snapshot(); const blob = zlib.gzipSync(Buffer.from(JSON.stringify(d)));
