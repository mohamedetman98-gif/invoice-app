'use strict';
const _v = process.versions.node.split('.').map(Number);
if (_v[0] < 22 || (_v[0] === 22 && _v[1] < 5)) { console.error('يلزم Node.js إصدار 22.5 أو أحدث. الإصدار الحالي: ' + process.versions.node); process.exit(1); }
/* =====================================================================
   خادم نظام أذون الفواتير — بدون أي مكتبات خارجية (Node.js 22.5+ فقط)
   قاعدة بيانات SQLite مدمجة + تحديث لحظي عبر SSE + صلاحيات على الخادم
   فكرة وتنفيذ: محمد صبري
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
  const now = Date.now(); if (!s.active || now - s.last > SESSION_MS) { Q('DELETE FROM sessions WHERE token=?').run(t); return null; }
  if (now - s.last > 300000) Q('UPDATE sessions SET last=? WHERE token=?').run(now, t);
  return { token: t, id: s.id, u: s.username, role: s.role, pm: s.pm ? JSON.parse(s.pm) : null, mustChange: !!s.must_change };
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
  Q('INSERT OR REPLACE INTO backups(at,label,by,n,u,blob) VALUES(?,?,?,?,?,?)').run(d.at, label, by, d.invs.length, d.users.length, blob);
  const keep = bkSettings().keep, all = Q('SELECT at FROM backups ORDER BY at DESC').all();
  for (const r of all.slice(keep)) Q('DELETE FROM backups WHERE at=?').run(r.at);
  return d.at;
}
const loadBackup = at => { const r = Q('SELECT blob FROM backups WHERE at=?').get(at); if (!r) throw new HttpError(404, 'النسخة غير موجودة'); return JSON.parse(zlib.gunzipSync(Buffer.from(r.blob)).toString()); };
const lastRestore = () => kvGet('bkhist', []).filter(x => x.kind === 'restore').sort((a, b) => a.when < b.when ? 1 : -1)[0];
function restoreCheck(actor, at) {
  if (actor.role === 'admin') return;
  if (!can(actor, 'restore')) throw new HttpError(403, 'ليست لديك صلاحية الاستعادة');
  if (!at || isNaN(Date.parse(at))) throw bad('تاريخ النسخة غير معروف');
  const h = lastRestore(); if (h && !(Date.parse(at) > Date.parse(h.from)))
    throw new HttpError(403, 'لا يمكن استعادة نسخة ليست أحدث من آخر نسخة تمت استعادتها. الاستعادة لتاريخ سابق من صلاحيات المدير فقط.');
}
function restore(d, actor, label, src) {
  if (!d || d.app !== 'invoice-server' || !Array.isArray(d.invs) || !Array.isArray(d.users)) throw bad('ملف نسخة احتياطية غير صالح (يجب أن يكون من نسخ هذا السيرفر)');
  restoreCheck(actor, d.at);
  const full = actor.role === 'admin';
  if (full && !d.users.some(u => u.role === 'admin' && u.active)) throw bad('النسخة لا تحتوي مديراً نشطاً، لن تتم الاستعادة');
  saveBackup('قبل الاستعادة (' + label + ')', actor.u);
  tx(() => {
    Q('DELETE FROM invoices').run(); INV.clear();
    for (const raw of d.invs) { const id = String(raw.Invoice_ID || '').trim(); if (!id) continue; const o = { ...newInv(id, raw) }; for (const k of ['Status', 'Paid_Status', 'PO_Number', 'Return_Number', 'Notes', 'First_Editor', 'User_Name']) if (raw[k] != null) o[k] = String(raw[k]); for (const k of ['First_At', 'ts', 'Received_At']) o[k] = +raw[k] || 0; if (!ST.includes(o.Status)) o.Status = 'Not Received'; if (!PAY.includes(o.Paid_Status)) o.Paid_Status = 'Unpaid'; o.PO_Number = cz(o.PO_Number); o.Return_Number = cz(o.Return_Number); INV.set(id, o); putInv(o); }
    kvSet('WH', Array.isArray(d.WH) ? d.WH : []); kvSet('DR', Array.isArray(d.DR) ? d.DR : []);
    if (full) {
      const ses = Q('SELECT s.token,u.username,s.created,s.last FROM sessions s JOIN users u ON u.id=s.user_id').all();
      Q('DELETE FROM sessions').run(); Q('DELETE FROM users').run();
      for (const u of d.users) Q('INSERT INTO users(username,salt,hash,role,active,pm,must_change) VALUES(?,?,?,?,?,?,?)').run(u.username, u.salt, u.hash, u.role, u.active ? 1 : 0, u.pm || null, u.must_change ? 1 : 0);
      for (const s of ses) { const u = Q('SELECT id,active FROM users WHERE username=?').get(s.username); if (u && u.active) Q('INSERT INTO sessions VALUES(?,?,?,?)').run(s.token, u.id, s.created, s.last); }
    }
    const h = kvGet('bkhist', []); h.unshift({ kind: 'restore', when: new Date().toISOString(), by: actor.u, from: d.at || '', label, scope: full ? 'كاملة (بيانات + مستخدمون)' : 'بيانات فقط' }); kvSet('bkhist', h.slice(0, 200));
  });
  broadcast('reload', { src });
  dropClients(c => !Q('SELECT 1 FROM users WHERE username=? AND active=1').get(c.u));
}
function bkTick() {
  try {
    const s = bkSettings(), now = Date.now();
    if (!s.lastSnap || now - Date.parse(s.lastSnap) >= s.hours * 36e5) { saveBackup('تلقائية (كل ' + s.hours + ' ساعة)', 'النظام (تلقائي)'); s.lastSnap = new Date().toISOString(); kvSet('bkset', { ...kvGet('bkset', {}), ...s }); }
    if (s.autoFile !== false && (!s.lastFile || now - Date.parse(s.lastFile) >= s.fileHours * 36e5)) {
      const t = new Date(), q = n => String(n).padStart(2, '0'), f = path.join(DATA_DIR, 'backups', `backup_${t.getFullYear()}-${q(t.getMonth() + 1)}-${q(t.getDate())}_${q(t.getHours())}${q(t.getMinutes())}.json.gz`);
      fs.writeFileSync(f, zlib.gzipSync(Buffer.from(JSON.stringify(snapshot()))));
      const files = fs.readdirSync(path.join(DATA_DIR, 'backups')).filter(x => x.endsWith('.json.gz')).sort();
      for (const x of files.slice(0, Math.max(0, files.length - s.keepFiles))) fs.unlinkSync(path.join(DATA_DIR, 'backups', x));
      kvSet('bkset', { ...kvGet('bkset', {}), lastFile: t.toISOString() });
    }
  } catch (e) { console.error('backup error', e); }
}
if (require.main === module) { setTimeout(bkTick, 2000).unref(); setInterval(bkTick, 60000).unref(); }

/* ---------------- HTTP ---------------- */
const send = async (req, res, status, obj, extraHeaders = {}) => {
  const body = Buffer.from(JSON.stringify(obj)); const h = { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', ...extraHeaders };
  if (body.length > 2048 && /\bgzip\b/.test(req.headers['accept-encoding'] || '')) { const z = await new Promise((ok, no) => zlib.gzip(body, (e, r) => e ? no(e) : ok(r))); h['Content-Encoding'] = 'gzip'; res.writeHead(status, h); return res.end(z); }
  res.writeHead(status, h); res.end(body);
};
const readBody = req => new Promise((ok, no) => { const ch = []; let n = 0; req.on('data', c => { n += c.length; if (n > MAX_BODY) { no(new HttpError(413, 'الحجم كبير جداً')); req.destroy(); } else ch.push(c); }); req.on('end', () => { try { ok(ch.length ? JSON.parse(Buffer.concat(ch).toString()) : {}); } catch (e) { no(bad('JSON غير صالح')); } }); req.on('error', no); });
const isHttps = req => req.socket.encrypted || (req.headers['x-forwarded-proto'] || '').split(',')[0] === 'https';
const SEC = { 'X-Content-Type-Options': 'nosniff', 'X-Frame-Options': 'DENY', 'Referrer-Policy': 'same-origin' };

const routes = [];
const route = (m, re, fn) => routes.push({ m, re, fn });
const adminOnly = u => { if (u.role !== 'admin') throw new HttpError(403, 'هذه العملية للمدير فقط'); };
const activeAdmins = excl => Q("SELECT COUNT(*) c FROM users WHERE role='admin' AND active=1 AND username<>?").get(excl || '').c;

route('POST', /^\/api\/login$/, async (req, res, ctx, b) => {
  const key = (req.socket.remoteAddress || '') + '|' + String(b.username || '').toLowerCase(); throttle(key);
  const r = Q('SELECT * FROM users WHERE username=?').get(String(b.username || '').trim());
  const ok = r && r.active && safeEq(await hashPw(String(b.password || ''), r.salt), r.hash);
  if (!ok) { failed(key); throw new HttpError(401, 'بيانات الدخول غير صحيحة أو الحساب مجمّد'); }
  fails.delete(key); const t = crypto.randomBytes(32).toString('hex'), now = Date.now();
  Q('INSERT INTO sessions VALUES(?,?,?,?)').run(t, r.id, now, now);
  const ck = `sid=${t}; HttpOnly; SameSite=Strict; Path=/; Max-Age=${Math.floor(SESSION_MS / 1000)}${isHttps(req) ? '; Secure' : ''}`;
  return [200, { me: pub(r) }, { 'Set-Cookie': ck }];
});
route('POST', /^\/api\/logout$/, async (req, res, ctx) => { if (ctx) Q('DELETE FROM sessions WHERE token=?').run(ctx.token); return [200, { ok: true }, { 'Set-Cookie': 'sid=; HttpOnly; SameSite=Strict; Path=/; Max-Age=0' }]; });
route('GET', /^\/api\/me$/, async (req, res, ctx) => { if (!ctx) throw new HttpError(401, 'غير مسجّل'); return [200, { me: pub(Q('SELECT * FROM users WHERE id=?').get(ctx.id)) }]; });
route('POST', /^\/api\/password$/, async (req, res, ctx, b) => {
  if (!ctx) throw new HttpError(401, 'غير مسجّل'); const r = Q('SELECT * FROM users WHERE id=?').get(ctx.id);
  if (!r.must_change && !(safeEq(await hashPw(String(b.current || ''), r.salt), r.hash))) throw new HttpError(403, 'كلمة المرور الحالية غير صحيحة');
  const n = String(b.next || ''); if (n.length < 6) throw bad('كلمة المرور الجديدة 6 أحرف على الأقل'); if (n === 'admin123') throw bad('اختر كلمة مرور مختلفة');
  const salt = newSalt(); Q('UPDATE users SET salt=?,hash=?,must_change=0 WHERE id=?').run(salt, await hashPw(n, salt), ctx.id);
  Q('DELETE FROM sessions WHERE user_id=? AND token<>?').run(ctx.id, ctx.token); return [200, { ok: true }];
});
route('GET', /^\/api\/state$/, async (req, res, ctx) => {
  const me = pub(Q('SELECT * FROM users WHERE id=?').get(ctx.id)); if (me.mustChange) throw new HttpError(403, 'يجب تغيير كلمة المرور أولاً');
  const o = { me, invs: [...INV.values()], WH: kvGet('WH', []), DR: kvGet('DR', []), now: Date.now() };
  if (ctx.role === 'admin') o.users = Q('SELECT * FROM users ORDER BY username').all().map(pub);
  return [200, o];
});
route('GET', /^\/api\/events$/, async (req, res, ctx) => {
  res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache, no-transform', Connection: 'keep-alive', 'X-Accel-Buffering': 'no', ...SEC });
  res.write('retry: 3000\n\nevent: hello\ndata: {}\n\n'); const c = { res, u: ctx.u, role: ctx.role }; clients.add(c); req.on('close', () => clients.delete(c)); return null;
});
route('POST', /^\/api\/invoices\/edit$/, async (req, res, ctx, b) => {
  need(ctx, 'edit'); const items = Array.isArray(b.items) ? b.items : []; if (!items.length || items.length > 5000) throw bad('لا توجد عناصر');
  const now = Date.now(), updated = [], conflicts = [];
  tx(() => { for (const it of items) { const id = String(it.id); const inv = INV.get(id); if (!inv) continue;
    if (it.expectedTs !== undefined && (+it.expectedTs || 0) !== (inv.ts || 0)) { conflicts.push({ id, current: inv }); continue; }
    const copy = { ...inv }; if (applyFields(copy, it.fields || {}, now, ctx)) { INV.set(id, copy); putInv(copy); updated.push(copy); } else updated.push(inv); } });
  const changed = updated.filter(x => x.ts === now); if (changed.length) broadcast('invs', { items: changed, src: req.headers['x-client'] || '' });
  return [200, { updated, conflicts }];
});
route('POST', /^\/api\/import\/erp$/, async (req, res, ctx, b) => {
  need(ctx, 'import'); const rows = Array.isArray(b.rows) ? b.rows : []; const added = []; let skipped = 0;
  tx(() => { for (const r of rows) { const id = String(r.Invoice_ID == null ? '' : r.Invoice_ID).trim().slice(0, 100); if (!id) continue; if (INV.has(id)) { skipped++; continue; } const o = newInv(id, r); INV.set(id, o); putInv(o); added.push(o); } });
  const big = added.length > 1500; if (added.length) broadcast(big ? 'reload' : 'invs', big ? { src: req.headers['x-client'] || '' } : { items: added, src: req.headers['x-client'] || '' });
  return [200, { added: added.length, skipped, items: big ? undefined : added, reload: big }];
});
route('POST', /^\/api\/master\/replace$/, async (req, res, ctx, b) => {
  need(ctx, 'replace'); const changes = Array.isArray(b.changes) ? b.changes : [], news = Array.isArray(b.news) ? b.news : [], remove = Array.isArray(b.remove) ? b.remove.map(String) : [];
  saveBackup('قبل استبدال الماستر داتا', ctx.u); const now = Date.now(); let ch = 0, nw = 0, rm = 0;
  tx(() => {
    for (const c of changes) { const inv = INV.get(String(c.id)); if (!inv) continue; const copy = { ...inv }, f = c.fields || {}; let did = false;
      for (const k of ERP_FIELDS) if (k !== 'Driver_Location' && k in f) { const v = sanitize(k, f[k]); if (copy[k] !== v) { copy[k] = v; did = true; } }
      const ef = {}; for (const k of EDITABLE) if (k in f) ef[k] = f[k]; if (applyFields(copy, ef, now, ctx)) did = true;
      if (did) { if (copy.ts !== now) { copy.First_Editor = copy.First_Editor || ctx.u; copy.First_At = copy.First_At || now; copy.User_Name = ctx.u; copy.ts = now; } INV.set(copy.Invoice_ID, copy); putInv(copy); ch++; } }
    for (const r of news) { const id = String(r.Invoice_ID == null ? '' : r.Invoice_ID).trim(); if (!id || INV.has(id)) continue; const o = newInv(id, r); const ef = {}; for (const k of EDITABLE) if (k in r) ef[k] = r[k]; applyFields(o, ef, now, { u: '' }); if (o.ts === now) { o.First_Editor = ''; o.User_Name = ''; o.ts = 0; o.First_At = 0; } INV.set(id, o); putInv(o); nw++; }
    for (const id of remove) if (INV.delete(id)) { Q('DELETE FROM invoices WHERE id=?').run(id); rm++; }
  });
  broadcast('reload', { src: req.headers['x-client'] || '' }); return [200, { changed: ch, added: nw, removed: rm }];
});
route('POST', /^\/api\/invoices\/delete-all$/, async (req, res, ctx, b) => {
  adminOnly(ctx); if (b.confirm !== 'حذف') throw bad('اكتب كلمة التأكيد'); saveBackup('قبل حذف كل الفواتير', ctx.u);
  tx(() => { Q('DELETE FROM invoices').run(); INV.clear(); }); broadcast('reload', { src: req.headers['x-client'] || '' }); return [200, { ok: true }];
});
route('PUT', /^\/api\/lookups$/, async (req, res, ctx, b) => {
  need(ctx, 'lookups'); const clean = (a, ks) => (Array.isArray(a) ? a : []).map(x => Object.fromEntries(ks.map(k => [k, String(x && x[k] != null ? x[k] : '').trim().slice(0, 200)]))).filter(x => x[ks[0]]);
  const WH = clean(b.WH, ['code', 'name']), DR = clean(b.DR, ['name', 'loc']); kvSet('WH', WH); kvSet('DR', DR);
  broadcast('lookups', { WH, DR, src: req.headers['x-client'] || '' }); return [200, { ok: true }];
});
/* المستخدمون (للمدير) */
route('GET', /^\/api\/users$/, async (req, res, ctx) => { adminOnly(ctx); return [200, { users: Q('SELECT * FROM users ORDER BY username').all().map(pub) }]; });
route('POST', /^\/api\/users$/, async (req, res, ctx, b) => { adminOnly(ctx); await addUser(b.username, b.password, b.role, true); broadcast('users', {}, c => c.role === 'admin'); return [200, { ok: true }]; });
route('PUT', /^\/api\/users\/(.+)$/, async (req, res, ctx, b, m) => {
  adminOnly(ctx); const name = decodeURIComponent(m[1]); const r = Q('SELECT * FROM users WHERE username=?').get(name); if (!r) throw new HttpError(404, 'المستخدم غير موجود');
  let role = r.role, active = r.active;
  if ('role' in b) { if (!ROLES.includes(b.role)) throw bad('دور غير صالح'); role = b.role; }
  if ('active' in b) active = b.active ? 1 : 0;
  if (r.role === 'admin' && r.active && (role !== 'admin' || !active) && activeAdmins(name) === 0) throw bad('لا يمكن تغيير أو تجميد آخر مدير في النظام');
  tx(() => {
    Q('UPDATE users SET role=?,active=? WHERE username=?').run(role, active, name);
    if ('pm' in b) { const pm = {}; if (b.pm && typeof b.pm === 'object') for (const k of PERMS) if (typeof b.pm[k] === 'boolean') pm[k] = b.pm[k]; Q('UPDATE users SET pm=? WHERE username=?').run(Object.keys(pm).length ? JSON.stringify(pm) : null, name); }
  });
  if (b.password) { if (String(b.password).length < 6) throw bad('كلمة المرور 6 أحرف على الأقل'); const salt = newSalt(); Q('UPDATE users SET salt=?,hash=?,must_change=1 WHERE username=?').run(salt, await hashPw(String(b.password), salt), name); Q('DELETE FROM sessions WHERE user_id=?').run(r.id); dropClients(c => c.u === name); }
  if (!active) { Q('DELETE FROM sessions WHERE user_id=?').run(r.id); dropClients(c => c.u === name); }
  broadcast('me', {}, c => c.u === name); broadcast('users', {}, c => c.role === 'admin'); return [200, { ok: true }];
});
route('DELETE', /^\/api\/users\/(.+)$/, async (req, res, ctx, b, m) => {
  adminOnly(ctx); const name = decodeURIComponent(m[1]); const r = Q('SELECT * FROM users WHERE username=?').get(name); if (!r) throw new HttpError(404, 'المستخدم غير موجود');
  if (name.toLowerCase() === ctx.u.toLowerCase()) throw bad('لا يمكنك حذف حسابك الحالي'); if (r.role === 'admin' && r.active && activeAdmins(name) === 0) throw bad('لا يمكن حذف آخر مدير');
  Q('DELETE FROM sessions WHERE user_id=?').run(r.id); Q('DELETE FROM users WHERE id=?').run(r.id); dropClients(c => c.u === name); broadcast('users', {}, c => c.role === 'admin'); return [200, { ok: true }];
});
/* النسخ الاحتياطي */
route('GET', /^\/api\/backups$/, async (req, res, ctx) => {
  if (!can(ctx, 'backup') && !can(ctx, 'restore')) throw new HttpError(403, 'ليست لديك صلاحية النسخ الاحتياطي');
  const o = { list: Q('SELECT at,label,by,n,u FROM backups ORDER BY at DESC').all(), lastRestore: lastRestore() ? { when: lastRestore().when, by: lastRestore().by, from: lastRestore().from } : null };
  if (ctx.role === 'admin') { o.settings = bkSettings(); o.hist = kvGet('bkhist', []).filter(x => x.kind === 'restore'); }
  else o.settings = { lastSnap: bkSettings().lastSnap }; return [200, o];
});
route('POST', /^\/api\/backups$/, async (req, res, ctx, b) => { need(ctx, 'backup'); const at = saveBackup('يدوية', ctx.u); kvSet('bkset', { ...kvGet('bkset', {}), lastSnap: at }); return [200, { at }]; });
route('GET', /^\/api\/backups\/(.+)\/file$/, async (req, res, ctx, b, m) => { need(ctx, 'backup'); const d = loadBackup(decodeURIComponent(m[1])); if (ctx.role !== 'admin') d.users = []; return [200, d]; });
route('GET', /^\/api\/backup-now$/, async (req, res, ctx) => { need(ctx, 'backup'); const d = snapshot(); if (ctx.role !== 'admin') d.users = []; return [200, d]; });
route('POST', /^\/api\/backups\/(.+)\/restore$/, async (req, res, ctx, b, m) => { const at = decodeURIComponent(m[1]); restore(loadBackup(at), ctx, new Date(at).toISOString(), req.headers['x-client'] || ''); return [200, { ok: true }]; });
route('POST', /^\/api\/restore-file$/, async (req, res, ctx, b) => { restore(b.data, ctx, 'ملف', req.headers['x-client'] || ''); return [200, { ok: true }]; });
route('PUT', /^\/api\/backup-settings$/, async (req, res, ctx, b) => {
  adminOnly(ctx); const s = {}; const pick = (k, vals) => { if (k in b) { const v = +b[k]; if (!vals.includes(v)) throw bad('قيمة غير مسموحة: ' + k); s[k] = v; } };
  pick('hours', [1, 2, 3, 4, 6, 8, 12, 24]); pick('fileHours', [1, 2, 3, 4, 6, 8, 12, 24, 48]); pick('keep', [15, 30, 60, 120]); if ('autoFile' in b) s.autoFile = !!b.autoFile;
  kvSet('bkset', { ...kvGet('bkset', {}), ...s }); return [200, { ok: true }];
});

const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.css': 'text/css', '.png': 'image/png', '.ico': 'image/x-icon', '.svg': 'image/svg+xml' };
const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url, 'http://x'), p = url.pathname;
    for (const [k, v] of Object.entries(SEC)) res.setHeader(k, v);
    if (p === '/healthz') { res.writeHead(200, { 'Content-Type': 'text/plain' }); return res.end('ok'); }
    if (p.startsWith('/api/')) {
      const ctx = sessionOf(req), r = routes.find(x => x.m === req.method && x.re.test(p));
      if (!r) throw new HttpError(404, 'غير موجود');
      const open = r.re.source.includes('login') || r.re.source.includes('logout') || r.re.source.includes('api\\/me');
      if (!ctx && !open) throw new HttpError(401, 'سجّل الدخول أولاً');
      if (ctx && ctx.mustChange && !(r.re.source.includes('password') || r.re.source.includes('logout') || r.re.source.includes('api\\/me'))) throw new HttpError(403, 'يجب تغيير كلمة المرور أولاً');
      if (req.method !== 'GET' && !req.headers['x-requested-with']) throw new HttpError(403, 'طلب غير مسموح');
      const body = ['POST', 'PUT', 'DELETE'].includes(req.method) ? await readBody(req) : {};
      const out = await r.fn(req, res, ctx, body, p.match(r.re));
      if (out === null) return; const [st, obj, hd] = out;
      if (/\/file$/.test(p) || p.endsWith('/backup-now')) { const t = new Date(); hd && 0; return send(req, res, st, obj, { 'Content-Disposition': `attachment; filename="invoice_backup_${t.toISOString().slice(0, 16).replace(/[:T]/g, '-')}.json"`, ...(hd || {}) }); }
      return send(req, res, st, obj, hd);
    }
    if (req.method !== 'GET') throw new HttpError(405, 'غير مسموح');
    let f = p === '/' ? '/index.html' : p; const full = path.join(PUBLIC, path.normalize(f).replace(/^(\.\.[\/\\])+/, ''));
    if (!full.startsWith(PUBLIC) || !fs.existsSync(full) || fs.statSync(full).isDirectory()) { res.writeHead(404); return res.end('Not found'); }
    const buf = fs.readFileSync(full), h = { 'Content-Type': MIME[path.extname(full)] || 'application/octet-stream', 'Cache-Control': 'no-store' };
    if (buf.length > 4096 && /\bgzip\b/.test(req.headers['accept-encoding'] || '')) { h['Content-Encoding'] = 'gzip'; res.writeHead(200, h); return res.end(zlib.gzipSync(buf)); }
    res.writeHead(200, h); res.end(buf);
  } catch (e) {
    if (res.headersSent) return res.end();
    const st = e instanceof HttpError ? e.status : 500; if (st === 500) console.error(e);
    send(req, res, st, { error: st === 500 ? 'خطأ داخلي في الخادم' : e.message, ...(e.extra || {}) });
  }
});
server.requestTimeout = 0; server.keepAliveTimeout = 65000;
if (require.main === module) {
  server.listen(PORT, HOST, () => console.log(`خادم أذون الفواتير يعمل على http://localhost:${PORT}  (البيانات: ${DATA_DIR})`));
  const stop = () => { try { db.exec('PRAGMA wal_checkpoint(TRUNCATE)'); } catch (_) {} process.exit(0); }; process.on('SIGINT', stop); process.on('SIGTERM', stop);
}
module.exports = { server };
