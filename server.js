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
const BACKUP_DIR = path.resolve(process.env.BACKUP_DIR || path.join(DATA_DIR, 'backups'));
const SESSION_MS = (+process.env.SESSION_DAYS || 14) * 864e5;
const MAX_BODY = 80 * 1024 * 1024;
fs.mkdirSync(BACKUP_DIR, { recursive: true });

/* ---------------- قاعدة البيانات ---------------- */
const db = new DatabaseSync(path.join(DATA_DIR, 'invoices.db'));
db.exec(`PRAGMA journal_mode=WAL; PRAGMA synchronous=NORMAL;
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT UNIQUE NOT NULL COLLATE NOCASE, salt TEXT, hash TEXT, role TEXT NOT NULL, active INTEGER NOT NULL DEFAULT 1, pm TEXT, must_change INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS sessions(token TEXT PRIMARY KEY, user_id INTEGER NOT NULL, created INTEGER, last INTEGER);
CREATE TABLE IF NOT EXISTS invoices(id TEXT PRIMARY KEY, data TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS kv(k TEXT PRIMARY KEY, v TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS backups(at TEXT PRIMARY KEY, label TEXT, by TEXT, n INTEGER, u INTEGER, blob BLOB);`);
try { db.exec('ALTER TABLE users ADD COLUMN phone TEXT'); } catch (_) {}
const Q = s => db.prepare(s);
function tx(fn) { db.exec('BEGIN IMMEDIATE'); try { const r = fn(); db.exec('COMMIT'); return r; } catch (e) { try { db.exec('ROLLBACK'); } catch (_) {} throw e; } }
const kvGet = (k, d) => { const r = Q('SELECT v FROM kv WHERE k=?').get(k); return r ? JSON.parse(r.v) : d; };
const kvSet = (k, v) => Q('INSERT INTO kv(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v').run(k, JSON.stringify(v));

/* ---------------- ثوابت ومنطق الأعمال (نفس قواعد الواجهة) ---------------- */
const ST = ['Not Received', 'Received', 'Returned', 'Partial'], PAY = ['Unpaid', 'Paid'];
const ERP_FIELDS = ['Invoice_Date', 'Customer_Code', 'Customer_Name', 'Address', 'Transaction_Type', 'Category1', 'Sales_Order', 'Driver_Name', 'Amount', 'Payment_Term', 'Customer_Category', 'Warehouse', 'Driver_Location', 'Registration'];
const EDITABLE = ['Status', 'Paid_Status', 'Pay_Method', 'Collected', 'PO_Number', 'Return_Number', 'Notes'];
const PM_DEFAULT = ['نقدي', 'بساطة', 'فوري'];
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
let invVer = 0, invCache = null;
const putInv = o => { invVer++; return Q('INSERT INTO invoices(id,data) VALUES(?,?) ON CONFLICT(id) DO UPDATE SET data=excluded.data').run(o.Invoice_ID, JSON.stringify(o)); };
function newInv(id, f) {
  const o = { Invoice_ID: id, Status: 'Not Received', Paid_Status: 'Unpaid', Pay_Method: '', Collected: 0, Collected_At: 0, Notes: '', Return_Number: '', PO_Number: '', First_Editor: '', First_At: 0, User_Name: '', ts: 0, Received_At: 0 };
  for (const k of ERP_FIELDS) if (k in f) o[k] = sanitize(k, f[k]);
  return o;
}
/* تطبيق الحقول القابلة للتعديل مع ختم المستخدم والوقت من الخادم */
function applyFields(inv, fields, now, user, opts) {
  let ch = false;
  for (const k of EDITABLE) {
    if (!(k in fields)) continue; let v = fields[k];
    if (k === 'Status') { if (!ST.includes(v)) throw bad('حالة استلام غير صالحة'); if (inv.Status !== v) { if (opts && opts.keepReceived) { if (v === 'Not Received') inv.Received_At = 0; } else if (v !== 'Not Received') { if (inv.Status === 'Not Received') inv.Received_At = now; } else inv.Received_At = 0; inv.Status = v; ch = true; } }
    else if (k === 'Paid_Status') { if (!PAY.includes(v)) throw bad('حالة دفع غير صالحة'); if ((inv.Paid_Status || 'Unpaid') !== v) { inv.Paid_Status = v; ch = true; } }
    else if (k === 'Pay_Method') { v = String(v == null ? '' : v).trim().slice(0, 40); if ((inv.Pay_Method || '') !== v) { inv.Pay_Method = v; ch = true; if (!v && inv.Collected) { inv.Collected = 0; inv.Collected_At = 0; } } }
    else if (k === 'Collected') {
      let n = (v === '' || v == null) ? 0 : Number(v);
      if (!isFinite(n) || n < 0) { if (opts && opts.lenient) continue; throw bad('القيمة المحصّلة غير صالحة'); }
      n = Math.round(n * 100) / 100; const amt = Number(inv.Amount) || 0;
      if (!inv.Pay_Method) n = 0; else if (amt > 0 && n > amt + 0.001) { if (opts && opts.lenient) n = amt; else throw bad('القيمة المحصّلة أكبر من قيمة الفاتورة'); }
      if ((Number(inv.Collected) || 0) !== n) { inv.Collected = n; inv.Collected_At = n > 0 ? now : 0; ch = true; }
    }
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
async function addUser(username, password, role, mustChange, phone) {
  if (!ROLES.includes(role)) throw bad('دور غير صالح'); username = String(username || '').trim();
  if (!/^[\w.\-@\u0600-\u06FF ]{2,40}$/.test(username)) throw bad('اسم المستخدم غير صالح (حروف وأرقام ونقطة وشرطة، من 2 إلى 40)');
  if (String(password || '').length < 6) throw bad('كلمة المرور 6 أحرف على الأقل');
  if (Q('SELECT 1 FROM users WHERE username=?').get(username)) throw bad('اسم المستخدم موجود بالفعل');
  const salt = newSalt(), hash = await hashPw(password, salt);
  Q('INSERT INTO users(username,salt,hash,role,active,must_change,phone) VALUES(?,?,?,?,1,?,?)').run(username, salt, hash, role, mustChange ? 1 : 0, String(phone || '').trim().slice(0, 30) || null);
}
/* ---------------- الحفظ الخارجي المشفّر (متوافق مع S3: Cloudflare R2 / AWS S3 / Backblaze B2 / Wasabi ...) ----------------
   يحمي البيانات من ضياع القرص المؤقت (مثل الخطة المجانية في Render): تُرفع لقطة مشفّرة بعد كل تغيير، وتُستعاد تلقائياً عند التشغيل على قرص فارغ. */
const S3 = { endpoint: (process.env.S3_ENDPOINT || '').replace(/\/+$/, ''), bucket: process.env.S3_BUCKET || '', ak: process.env.S3_ACCESS_KEY || '', sk: process.env.S3_SECRET_KEY || '', region: process.env.S3_REGION || 'auto', prefix: (process.env.S3_PREFIX || 'invoice-system/').replace(/^\/+/, '') };
const SYNC_KEY = process.env.SYNC_KEY || '';
const syncOn = () => !!(S3.endpoint && S3.bucket && S3.ak && S3.sk && SYNC_KEY);
const SYNC_DEBOUNCE = +process.env.SYNC_DEBOUNCE_MS || 20000;
const sha256hex = b => crypto.createHash('sha256').update(b).digest('hex'), hmac = (k, d) => crypto.createHmac('sha256', k).update(d).digest();
function awsSign(o) {
  const date = o.amzDate.slice(0, 8), h = { ...o.headers, host: o.host, 'x-amz-date': o.amzDate };
  const names = Object.keys(h).map(x => x.toLowerCase()).sort(), low = Object.fromEntries(Object.entries(h).map(([k, v]) => [k.toLowerCase(), v]));
  const canonHeaders = names.map(n => n + ':' + String(low[n]).trim().replace(/\s+/g, ' ') + '\n').join(''), signedHeaders = names.join(';');
  const canonReq = [o.method, o.path, o.query || '', canonHeaders, signedHeaders, o.payloadHash].join('\n');
  const scope = `${date}/${o.region}/${o.service}/aws4_request`, sts = ['AWS4-HMAC-SHA256', o.amzDate, scope, sha256hex(canonReq)].join('\n');
  const kSign = hmac(hmac(hmac(hmac('AWS4' + o.secretKey, date), o.region), o.service), 'aws4_request'), signature = hmac(kSign, sts).toString('hex');
  return { authorization: `AWS4-HMAC-SHA256 Credential=${o.accessKey}/${scope}, SignedHeaders=${signedHeaders}, Signature=${signature}`, signature };
}
async function s3Req(method, key, body) {
  const u = new URL(S3.endpoint), path = '/' + S3.bucket + '/' + key.split('/').map(encodeURIComponent).join('/'), amz = new Date().toISOString().replace(/[:-]|\.\d{3}/g, ''), ph = sha256hex(body || '');
  const sg = awsSign({ method, host: u.host, path, query: '', headers: { 'x-amz-content-sha256': ph }, payloadHash: ph, accessKey: S3.ak, secretKey: S3.sk, region: S3.region, service: 's3', amzDate: amz });
  const r = await fetch(u.origin + path, { method, headers: { 'x-amz-content-sha256': ph, 'x-amz-date': amz, Authorization: sg.authorization }, body: body || undefined, signal: AbortSignal.timeout(60000) });
  if (r.status === 404 && method === 'GET') return null;
  if (!r.ok) throw new Error(`S3 ${method} ${r.status}: ${(await r.text()).slice(0, 200)}`);
  return method === 'GET' ? Buffer.from(await r.arrayBuffer()) : true;
}
const MAGIC = Buffer.from('INV1');
function encBuf(plain) { const salt = crypto.randomBytes(16), iv = crypto.randomBytes(12), key = crypto.scryptSync(SYNC_KEY, salt, 32), c = crypto.createCipheriv('aes-256-gcm', key, iv), ct = Buffer.concat([c.update(plain), c.final()]); return Buffer.concat([MAGIC, salt, iv, c.getAuthTag(), ct]); }
function decBuf(buf) { if (buf.subarray(0, 4).compare(MAGIC) !== 0) throw new Error('صيغة ملف التخزين الخارجي غير معروفة'); const salt = buf.subarray(4, 20), iv = buf.subarray(20, 32), tag = buf.subarray(32, 48), ct = buf.subarray(48), key = crypto.scryptSync(SYNC_KEY, salt, 32), d = crypto.createDecipheriv('aes-256-gcm', key, iv); d.setAuthTag(tag); try { return Buffer.concat([d.update(ct), d.final()]); } catch (_) { throw new Error('تعذّر فك التشفير: SYNC_KEY غير صحيح أو الملف تالف'); } }
function syncState() { return { app: 'invoice-sync', v: 1, at: new Date().toISOString(), users: Q('SELECT username,salt,hash,role,active,pm,must_change,phone FROM users').all(), invs: [...INV.values()], kv: Object.fromEntries(Q('SELECT k,v FROM kv').all().map(r => [r.k, JSON.parse(r.v)])) }; }
function applySyncState(d) {
  if (!d || d.app !== 'invoice-sync' || !Array.isArray(d.users) || !Array.isArray(d.invs)) throw new Error('محتوى التخزين الخارجي غير صالح');
  tx(() => { Q('DELETE FROM sessions').run(); Q('DELETE FROM users').run(); Q('DELETE FROM invoices').run(); Q('DELETE FROM kv').run(); INV.clear(); invVer++;
    for (const u of d.users) Q('INSERT INTO users(username,salt,hash,role,active,pm,must_change,phone) VALUES(?,?,?,?,?,?,?,?)').run(u.username, u.salt, u.hash, u.role, u.active ? 1 : 0, u.pm || null, u.must_change ? 1 : 0, u.phone || null);
    for (const o of d.invs) { INV.set(o.Invoice_ID, o); putInv(o); } for (const [k, v] of Object.entries(d.kv || {})) kvSet(k, v); });
}
let syncDirty = false, syncTimer = null, syncBusy = false; const syncStat = { lastOk: null, lastErr: null, lastErrAt: null, uploads: 0 };
function markDirty() { if (!syncOn()) return; syncDirty = true; if (!syncTimer) { syncTimer = setTimeout(() => { syncTimer = null; doSync().catch(() => {}); }, SYNC_DEBOUNCE); if (syncTimer.unref) syncTimer.unref(); } }
async function doSync(force) {
  if (!syncOn() || syncBusy || (!syncDirty && !force)) return; syncBusy = true; syncDirty = false;
  try { await s3Req('PUT', S3.prefix + 'state.enc', encBuf(zlib.gzipSync(Buffer.from(JSON.stringify(syncState()))))); syncStat.lastOk = Date.now(); syncStat.lastErr = null; syncStat.uploads++; }
  catch (e) { syncDirty = true; syncStat.lastErr = String(e.message || e); syncStat.lastErrAt = Date.now(); console.error('خطأ في الحفظ الخارجي:', syncStat.lastErr); }
  finally { syncBusy = false; }
}
const startInfo = { startedAt: Date.now(), origin: 'existing' };
async function bootstrap() {
  if (Q('SELECT COUNT(*) c FROM users').get().c) return;
  if (syncOn()) {
    const buf = await s3Req('GET', S3.prefix + 'state.enc'); /* أي خطأ شبكي/مصادقة يوقف الإقلاع حتى لا نكتب فوق البيانات الخارجية بحالة فارغة */
    if (buf) { applySyncState(JSON.parse(zlib.gunzipSync(decBuf(buf)).toString())); startInfo.origin = 'restored'; console.log(`تمت استعادة البيانات من التخزين الخارجي (${INV.size} فاتورة)`); return; }
  }
  const pw = process.env.ADMIN_PASSWORD || crypto.randomBytes(6).toString('base64url');
  await addUser('admin', pw, 'admin', true); startInfo.origin = 'fresh'; markDirty();
  console.log('\n==============================================================\n  تم إنشاء حساب المدير لأول مرة:\n  اسم المستخدم: admin\n  كلمة المرور المؤقتة: ' + pw + '\n  (سيُطلب منك تغييرها عند أول دخول — سجّلها الآن فلن تظهر مرة أخرى)\n==============================================================\n');
}
function storageWarn() { return !!process.env.RENDER && !process.env.PERSISTENT_STORAGE && !syncOn(); }
function keepAlive() { const url = process.env.KEEP_ALIVE_URL || (process.env.KEEP_ALIVE === '1' ? process.env.RENDER_EXTERNAL_URL : ''); if (!url) return; const t = setInterval(() => { fetch(url.replace(/\/+$/, '') + '/healthz', { signal: AbortSignal.timeout(20000) }).catch(() => {}); }, 10 * 60 * 1000); t.unref(); console.log('keep-alive: ping كل 10 دقائق →', url); }
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
const secretKey = () => { let k = kvGet('secret', null); if (!k) { k = crypto.randomBytes(32).toString('hex'); kvSet('secret', k); } return k; };
function bodyHash(d) { const h = crypto.createHash('sha256'); for (const inv of d.invs) h.update(JSON.stringify(inv)); h.update(JSON.stringify([d.WH, d.DR, d.PM, d.CFG])); return h.digest('hex'); }
const signB = d => hmac(secretKey(), d.at + '|' + bodyHash(d)).toString('hex');
/* لقطة خفيفة: لا تنسخ الفواتير في نص واحد ضخم (يوفّر الذاكرة مع عشرات آلاف الفواتير) */
function dBase() { return { app: 'invoice-server', v: 5, at: new Date().toISOString(), users: Q('SELECT username,salt,hash,role,active,pm,must_change,phone FROM users').all(), items: [...INV.values()], WH: kvGet('WH', []), DR: kvGet('DR', []), PM: kvGet('PM', PM_DEFAULT), CFG: kvGet('CFG', {}) }; }
async function* backupChunks(d, strip) {
  const h = crypto.createHash('sha256'), items = d.items || d.invs;
  yield `{"app":${JSON.stringify(d.app)},"v":${d.v},"at":${JSON.stringify(d.at)},"users":${JSON.stringify(strip ? [] : d.users)},"invs":[`;
  let buf = [], first = true;
  for (const inv of items) { const t = JSON.stringify(inv); h.update(t); buf.push(t); if (buf.length >= 400) { yield (first ? '' : ',') + buf.join(','); first = false; buf = []; await new Promise(r => setImmediate(r)); } }
  if (buf.length) yield (first ? '' : ',') + buf.join(',');
  h.update(JSON.stringify([d.WH, d.DR, d.PM, d.CFG]));
  yield `],"WH":${JSON.stringify(d.WH)},"DR":${JSON.stringify(d.DR)},"PM":${JSON.stringify(d.PM)},"CFG":${JSON.stringify(d.CFG)},"sig":"${hmac(secretKey(), d.at + '|' + h.digest('hex')).toString('hex')}"}`;
}
async function gzBuf(d, strip) { const gz = zlib.createGzip({ level: 6 }), chunks = []; gz.on('data', c => chunks.push(c)); const done = new Promise((ok, no) => { gz.on('end', ok); gz.on('error', no); }); for await (const t of backupChunks(d, strip)) { if (!gz.write(t)) await new Promise(r => gz.once('drain', r)); } gz.end(); await done; return Buffer.concat(chunks); }
async function streamBackup(req, res, d, strip, filename) {
  const gzOk = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
  res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store', 'Content-Disposition': `attachment; filename="${filename}"`, ...(gzOk ? { 'Content-Encoding': 'gzip' } : {}) });
  const w = gzOk ? zlib.createGzip({ level: 5 }) : res; if (gzOk) w.pipe(res);
  for await (const t of backupChunks(d, strip)) { if (!w.write(t)) await new Promise(r => w.once('drain', r)); } w.end();
}
const bkName = () => { const t = new Date(), q = n => String(n).padStart(2, '0'); return `invoice_backup_${t.getFullYear()}-${q(t.getMonth() + 1)}-${q(t.getDate())}_${q(t.getHours())}${q(t.getMinutes())}.json`; };
async function saveBackup(label, by) {
  const d = dBase(), blob = await gzBuf(d);
  Q('INSERT OR REPLACE INTO backups(at,label,by,n,u,blob) VALUES(?,?,?,?,?,?)').run(d.at, label, by, d.items.length, d.users.length, blob);
  const keep = bkSettings().keep, all = Q('SELECT at FROM backups ORDER BY at DESC').all();
  for (const r of all.slice(keep)) Q('DELETE FROM backups WHERE at=?').run(r.at);
  return d.at;
}
async function invoicesGz() {
  if (invCache && invCache.ver === invVer) return invCache.p; const ver = invVer;
  const p = (async () => { const gz = zlib.createGzip({ level: 5 }), chunks = []; gz.on('data', c => chunks.push(c)); const done = new Promise((ok, no) => { gz.on('end', ok); gz.on('error', no); });
    gz.write('['); let first = true, buf = []; for (const inv of [...INV.values()]) { buf.push(JSON.stringify(inv)); if (buf.length >= 400) { if (!gz.write((first ? '' : ',') + buf.join(','))) await new Promise(r => gz.once('drain', r)); first = false; buf = []; await new Promise(r => setImmediate(r)); } }
    if (buf.length) gz.write((first ? '' : ',') + buf.join(',')); gz.write(']'); gz.end(); await done; return Buffer.concat(chunks); })();
  invCache = { ver, p }; return p;
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
async function restore(d, actor, label, src, trusted) {
  if (!d || d.app !== 'invoice-server' || !Array.isArray(d.invs) || !Array.isArray(d.users)) throw bad('ملف نسخة احتياطية غير صالح (يجب أن يكون من نسخ هذا السيرفر)');
  restoreCheck(actor, d.at);
  if (actor.role !== 'admin' && !trusted && !(d.sig && safeEq(String(d.sig), signB(d)))) throw bad('ملف النسخة غير موثّق (عُدّل أو لم يُنشأ من هذا الخادم)، لذلك لا يمكن الاعتماد على تاريخ إنشائه');
  const full = actor.role === 'admin';
  if (full && !d.users.some(u => u.role === 'admin' && u.active)) throw bad('النسخة لا تحتوي مديراً نشطاً، لن تتم الاستعادة');
  await saveBackup('قبل الاستعادة (' + label + ')', actor.u);
  tx(() => {
    Q('DELETE FROM invoices').run(); INV.clear(); invVer++;
    for (const raw of d.invs) { const id = String(raw.Invoice_ID || '').trim(); if (!id) continue; const o = { ...newInv(id, raw) }; for (const k of ['Status', 'Paid_Status', 'Pay_Method', 'PO_Number', 'Return_Number', 'Notes', 'First_Editor', 'User_Name']) if (raw[k] != null) o[k] = String(raw[k]); for (const k of ['First_At', 'ts', 'Received_At', 'Collected', 'Collected_At']) o[k] = +raw[k] || 0; if (!ST.includes(o.Status)) o.Status = 'Not Received'; if (!PAY.includes(o.Paid_Status)) o.Paid_Status = 'Unpaid'; o.PO_Number = cz(o.PO_Number); o.Return_Number = cz(o.Return_Number); INV.set(id, o); putInv(o); }
    kvSet('WH', Array.isArray(d.WH) ? d.WH : []); kvSet('DR', Array.isArray(d.DR) ? d.DR : []); if (Array.isArray(d.PM)) kvSet('PM', d.PM); if (d.CFG && typeof d.CFG === 'object') kvSet('CFG', d.CFG);
    if (full) {
      const ses = Q('SELECT s.token,u.username,s.created,s.last FROM sessions s JOIN users u ON u.id=s.user_id').all();
      Q('DELETE FROM sessions').run(); Q('DELETE FROM users').run();
      for (const u of d.users) Q('INSERT INTO users(username,salt,hash,role,active,pm,must_change,phone) VALUES(?,?,?,?,?,?,?,?)').run(u.username, u.salt, u.hash, u.role, u.active ? 1 : 0, u.pm || null, u.must_change ? 1 : 0, u.phone || null);
      for (const s of ses) { const u = Q('SELECT id,active FROM users WHERE username=?').get(s.username); if (u && u.active) Q('INSERT INTO sessions VALUES(?,?,?,?)').run(s.token, u.id, s.created, s.last); }
    }
    const h = kvGet('bkhist', []); h.unshift({ kind: 'restore', when: new Date().toISOString(), by: actor.u, from: d.at || '', label, scope: full ? 'كاملة (بيانات + مستخدمون)' : 'بيانات فقط' }); kvSet('bkhist', h.slice(0, 200));
  });
  broadcast('reload', { src });
  dropClients(c => !Q('SELECT 1 FROM users WHERE username=? AND active=1').get(c.u));
}
async function bkTick() {
  try {
    const s = bkSettings(), now = Date.now();
    if (!s.lastSnap || now - Date.parse(s.lastSnap) >= s.hours * 36e5) { await saveBackup('تلقائية (كل ' + s.hours + ' ساعة)', 'النظام (تلقائي)'); s.lastSnap = new Date().toISOString(); kvSet('bkset', { ...kvGet('bkset', {}), ...s }); markDirty(); }
    if (s.autoFile !== false && (!s.lastFile || now - Date.parse(s.lastFile) >= s.fileHours * 36e5)) {
      const t = new Date(), q = n => String(n).padStart(2, '0'), f = path.join(BACKUP_DIR, `backup_${t.getFullYear()}-${q(t.getMonth() + 1)}-${q(t.getDate())}_${q(t.getHours())}${q(t.getMinutes())}.json.gz`);
      fs.mkdirSync(BACKUP_DIR, { recursive: true }); const gz = await gzBuf(dBase()); fs.writeFileSync(f, gz);
      if (syncOn()) s3Req('PUT', S3.prefix + 'backups/' + path.basename(f).replace('.json.gz', '.enc'), encBuf(gz)).catch(e => console.error('رفع النسخة الاحتياطية للتخزين الخارجي فشل:', e.message));
      const files = fs.readdirSync(BACKUP_DIR).filter(x => x.endsWith('.json.gz')).sort();
      for (const x of files.slice(0, Math.max(0, files.length - s.keepFiles))) fs.unlinkSync(path.join(BACKUP_DIR, x));
      kvSet('bkset', { ...kvGet('bkset', {}), lastFile: t.toISOString() }); markDirty();
    }
  } catch (e) { console.error('backup error', e); }
}

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
  const o = { me, invsVer: invVer, WH: kvGet('WH', []), DR: kvGet('DR', []), PM: kvGet('PM', PM_DEFAULT), CFG: kvGet('CFG', {}), now: Date.now() };
  if (ctx.role === 'admin') { o.users = Q('SELECT * FROM users ORDER BY username').all().map(x => ({ ...pub(x), phone: x.phone || '' })); o.storageWarn = storageWarn(); }
  return [200, o];
});
route('GET', /^\/api\/events$/, async (req, res, ctx) => {
  res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache, no-transform', Connection: 'keep-alive', 'X-Accel-Buffering': 'no', ...SEC });
  res.write('retry: 3000\n\nevent: hello\ndata: {}\n\n'); const c = { res, u: ctx.u, role: ctx.role }; clients.add(c); req.on('close', () => clients.delete(c)); return null;
});
route('POST', /^\/api\/invoices\/edit$/, async (req, res, ctx, b) => {
  need(ctx, 'edit'); const items = Array.isArray(b.items) ? b.items : []; if (!items.length || items.length > 5000) throw bad('لا توجد عناصر');
  const now = Date.now(), updated = [], conflicts = [], before = [];
  tx(() => { for (const it of items) { const id = String(it.id); const inv = INV.get(id); if (!inv) continue;
    if (it.expectedTs !== undefined && (+it.expectedTs || 0) !== (inv.ts || 0)) { conflicts.push({ id, current: inv }); continue; }
    const copy = { ...inv }; if (applyFields(copy, it.fields || {}, now, ctx)) { INV.set(id, copy); putInv(copy); updated.push(copy); before.push({ id, before: inv, afterTs: now }); } else updated.push(inv); } });
  const changed = updated.filter(x => x.ts === now); if (changed.length) { pushUndo(ctx.u, before); broadcast('invs', { items: changed, src: req.headers['x-client'] || '' }); }
  return [200, { updated, conflicts }];
});
const undoLog = new Map();
function pushUndo(u, items) { const a = (undoLog.get(u) || []).filter(o => Date.now() - o.at < 864e5); a.push({ items, at: Date.now() }); while (a.length > 30) a.shift(); undoLog.set(u, a); }
route('POST', /^\/api\/undo$/, async (req, res, ctx) => {
  need(ctx, 'edit'); const a = (undoLog.get(ctx.u) || []).filter(o => Date.now() - o.at < 864e5); undoLog.set(ctx.u, a); const op = a.pop();
  if (!op) throw new HttpError(404, 'لا توجد حركة تعديل للتراجع عنها');
  const restored = []; tx(() => { for (const it of op.items) { const cur = INV.get(it.id); if (!cur || (cur.ts || 0) !== it.afterTs) continue; INV.set(it.id, it.before); putInv(it.before); restored.push(it.before); } });
  if (!restored.length) throw new HttpError(409, 'لا يمكن التراجع: الفواتير عُدّلت بعد ذلك من مستخدم آخر');
  broadcast('invs', { items: restored, src: req.headers['x-client'] || '' }); return [200, { updated: restored }];
});
route('PUT', /^\/api\/settings$/, async (req, res, ctx, b) => {
  adminOnly(ctx); const c = b.CFG && typeof b.CFG === 'object' ? b.CFG : {}, clean = {};
  if (c.terms && typeof c.terms === 'object') { clean.terms = {}; for (const [k, v] of Object.entries(c.terms)) if (/^\w{1,40}$/.test(k) && typeof v === 'string' && v.trim()) clean.terms[k] = v.trim().slice(0, 120); }
  if (c.sound && typeof c.sound === 'object') clean.sound = { ok: String(c.sound.ok || 'p1').slice(0, 8), err: String(c.sound.err || 'p1').slice(0, 8), vol: Math.min(0.5, Math.max(0.05, +c.sound.vol || 0.18)) };
  if (c.layout && typeof c.layout === 'object') { clean.layout = {}; for (const n of ['dash', 'facts', 'drv']) if (Array.isArray(c.layout[n])) clean.layout[n] = c.layout[n].slice(0, 40).map(x => ({ k: String((x && x.k) || '').slice(0, 40), on: !!(x && x.on) })); }
  kvSet('CFG', clean); broadcast('settings', { CFG: clean, src: req.headers['x-client'] || '' }); return [200, { ok: true }];
});
route('POST', /^\/api\/maintenance\/clear-received$/, async (req, res, ctx) => {
  adminOnly(ctx); await saveBackup('قبل مسح تواريخ الاستلام', ctx.u);
  tx(() => { for (const [id, inv] of INV) if (inv.Received_At) { const c = { ...inv, Received_At: 0 }; INV.set(id, c); putInv(c); } });
  broadcast('reload', { src: req.headers['x-client'] || '' }); return [200, { ok: true }];
});
route('GET', /^\/api\/sync-status$/, async (req, res, ctx) => {
  adminOnly(ctx); return [200, { configured: syncOn(), endpoint: S3.endpoint.replace(/^https?:\/\//, ''), bucket: S3.bucket, lastOk: syncStat.lastOk, lastErr: syncStat.lastErr, lastErrAt: syncStat.lastErrAt, pending: syncDirty, uploads: syncStat.uploads, origin: startInfo.origin, startedAt: startInfo.startedAt,
    onRender: !!process.env.RENDER, persistentDeclared: !!process.env.PERSISTENT_STORAGE, ephemeralWarning: storageWarn(), keepAlive: !!(process.env.KEEP_ALIVE_URL || process.env.KEEP_ALIVE === '1') }];
});
route('POST', /^\/api\/sync-now$/, async (req, res, ctx) => { adminOnly(ctx); if (!syncOn()) throw bad('الحفظ الخارجي غير مُفعّل'); await doSync(true); if (syncStat.lastErr) throw new HttpError(502, 'فشل الرفع: ' + syncStat.lastErr); return [200, { ok: true, lastOk: syncStat.lastOk }]; });
const nph = x => String(x || '').replace(/\D/g, '').replace(/^0+/, '').slice(-9);
const genTemp = () => { const al = 'ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnpqrstuvwxyz23456789'; return Array.from({ length: 8 }, () => al[crypto.randomInt(al.length)]).join(''); };
const SMS = { provider: (process.env.SMS_PROVIDER || '').toLowerCase(), sid: process.env.TWILIO_SID || '', token: process.env.TWILIO_TOKEN || '', from: process.env.TWILIO_FROM || '', twilioUrl: (process.env.TWILIO_API_URL || 'https://api.twilio.com').replace(/\/+$/, ''), hook: process.env.SMS_WEBHOOK_URL || '', hookToken: process.env.SMS_WEBHOOK_TOKEN || '', cc: process.env.SMS_DEFAULT_COUNTRY || '20' };
const smsOn = () => !!((SMS.provider === 'twilio' && SMS.sid && SMS.token && SMS.from) || (SMS.provider === 'webhook' && SMS.hook));
function e164(p) { const raw = String(p || '').trim(), d = raw.replace(/\D/g, ''); if (!d) return ''; if (raw.startsWith('+')) return '+' + d; if (d.startsWith('00')) return '+' + d.slice(2); if (d.startsWith('0')) return '+' + SMS.cc + d.slice(1); if (d.startsWith(SMS.cc)) return '+' + d; return '+' + SMS.cc + d; }
async function sendSms(to, text) {
  const num = e164(to);
  if (SMS.provider === 'twilio') { const r = await fetch(`${SMS.twilioUrl}/2010-04-01/Accounts/${SMS.sid}/Messages.json`, { method: 'POST', headers: { Authorization: 'Basic ' + Buffer.from(SMS.sid + ':' + SMS.token).toString('base64'), 'Content-Type': 'application/x-www-form-urlencoded' }, body: new URLSearchParams({ To: num, From: SMS.from, Body: text }), signal: AbortSignal.timeout(20000) }); if (!r.ok) throw new Error('Twilio ' + r.status + ': ' + (await r.text()).slice(0, 150)); return; }
  if (SMS.provider === 'webhook') { const r = await fetch(SMS.hook, { method: 'POST', headers: { 'Content-Type': 'application/json', ...(SMS.hookToken ? { Authorization: 'Bearer ' + SMS.hookToken } : {}) }, body: JSON.stringify({ to: num, message: text }), signal: AbortSignal.timeout(20000) }); if (!r.ok) throw new Error('SMS webhook ' + r.status); return; }
  throw new Error('SMS غير مُفعّل');
}
const fgRate = new Map();
function fgThrottle(key, max) { const now = Date.now(), a = (fgRate.get(key) || []).filter(t => now - t < 3600e3); if (a.length >= max) throw new HttpError(429, 'محاولات كثيرة. حاول لاحقاً'); a.push(now); fgRate.set(key, a); }
route('POST', /^\/api\/forgot$/, async (req, res, ctx, b) => {
  const u = String(b.username || '').trim(), ph = nph(b.phone); fgThrottle('ip:' + (req.socket.remoteAddress || ''), 10); if (u) fgThrottle('u:' + u.toLowerCase(), 3);
  const generic = [200, { ok: true, message: 'إن كانت البيانات صحيحة فسيصلك رد على هاتفك المسجّل (أو سيتواصل معك المدير).' }];
  if (!u || !ph) return generic;
  const r = Q('SELECT * FROM users WHERE username=? AND active=1').get(u); if (!r || !r.phone || nph(r.phone) !== ph) return generic;
  const list = kvGet('resets', []).filter(x => !(x.u === r.username && x.status === 'pending') && Date.now() - x.at < 14 * 864e5);
  const entry = { id: crypto.randomBytes(4).toString('hex'), u: r.username, phone: r.phone, at: Date.now(), status: 'pending' };
  if (smsOn()) { const pw = genTemp(); try { await sendSms(r.phone, `كلمة المرور المؤقتة لنظام أذون الفواتير: ${pw}\nسيُطلب منك تغييرها عند الدخول.`); const salt = newSalt(); Q('UPDATE users SET salt=?,hash=?,must_change=1 WHERE id=?').run(salt, await hashPw(pw, salt), r.id); Q('DELETE FROM sessions WHERE user_id=?').run(r.id); dropClients(c => c.u === r.username); entry.status = 'sent'; } catch (e) { entry.status = 'failed'; entry.err = String(e.message).slice(0, 150); console.error('فشل إرسال SMS:', e.message); } }
  list.unshift(entry); kvSet('resets', list.slice(0, 100)); markDirty(); if (entry.status !== 'sent') broadcast('resets', {}, c => c.role === 'admin'); return generic;
});
route('GET', /^\/api\/resets$/, async (req, res, ctx) => { adminOnly(ctx); return [200, { resets: kvGet('resets', []), smsOn: smsOn() }]; });
route('POST', /^\/api\/resets\/(\w+)\/generate$/, async (req, res, ctx, b, m) => {
  adminOnly(ctx); const list = kvGet('resets', []), e = list.find(x => x.id === m[1]); if (!e) throw new HttpError(404, 'الطلب غير موجود');
  const r = Q('SELECT * FROM users WHERE username=?').get(e.u); if (!r) throw new HttpError(404, 'المستخدم غير موجود');
  const pw = genTemp(), salt = newSalt(); Q('UPDATE users SET salt=?,hash=?,must_change=1 WHERE id=?').run(salt, await hashPw(pw, salt), r.id); Q('DELETE FROM sessions WHERE user_id=?').run(r.id); dropClients(c => c.u === r.username);
  e.status = 'done'; kvSet('resets', list); return [200, { username: r.username, phone: r.phone, password: pw }];
});
route('DELETE', /^\/api\/resets\/(\w+)$/, async (req, res, ctx, b, m) => { adminOnly(ctx); kvSet('resets', kvGet('resets', []).filter(x => x.id !== m[1])); return [200, { ok: true }]; });
route('PUT', /^\/api\/paymethods$/, async (req, res, ctx, b) => {
  adminOnly(ctx); const PM = [...new Set((Array.isArray(b.PM) ? b.PM : []).map(x => String(x || '').trim().slice(0, 40)).filter(Boolean))].slice(0, 30);
  kvSet('PM', PM); broadcast('paymethods', { PM, src: req.headers['x-client'] || '' }); return [200, { ok: true }];
});
route('POST', /^\/api\/import\/erp$/, async (req, res, ctx, b) => {
  need(ctx, 'import'); const rows = Array.isArray(b.rows) ? b.rows : []; const added = []; let skipped = 0, conflicts = 0, invalid = 0;
  tx(() => { for (const r of rows) {
    const id = String(r.Invoice_ID == null ? '' : r.Invoice_ID).trim().slice(0, 100), d = sanitize('Invoice_Date', r.Invoice_Date), c = String(r.Customer_Code == null ? '' : r.Customer_Code).trim();
    if (!id || !d || !c) { invalid++; continue; }
    const ex = INV.get(id); if (ex) { if ((ex.Invoice_Date || '') === d && String(ex.Customer_Code || '').trim() === c) skipped++; else conflicts++; continue; }
    const o = newInv(id, r); INV.set(id, o); putInv(o); added.push(o); } });
  const big = added.length > 1500; if (added.length) broadcast(big ? 'reload' : 'invs', big ? { src: req.headers['x-client'] || '' } : { items: added, src: req.headers['x-client'] || '' });
  return [200, { added: added.length, skipped, conflicts, invalid, items: big ? undefined : added, reload: big }];
});
route('POST', /^\/api\/master\/replace$/, async (req, res, ctx, b) => {
  need(ctx, 'replace'); const changes = Array.isArray(b.changes) ? b.changes : [], news = Array.isArray(b.news) ? b.news : [], remove = Array.isArray(b.remove) ? b.remove.map(String) : [];
  await saveBackup('قبل استبدال الماستر داتا', ctx.u); const now = Date.now(); let ch = 0, nw = 0, rm = 0;
  tx(() => {
    for (const c of changes) { const inv = INV.get(String(c.id)); if (!inv) continue; const copy = { ...inv }, f = c.fields || {}; let did = false;
      for (const k of ERP_FIELDS) if (k !== 'Driver_Location' && k in f) { const v = sanitize(k, f[k]); if (copy[k] !== v) { copy[k] = v; did = true; } }
      const ef = {}; for (const k of EDITABLE) if (k in f) ef[k] = f[k]; if (applyFields(copy, ef, now, ctx, { keepReceived: true, lenient: true })) did = true;
      if (did) { if (copy.ts !== now) { copy.First_Editor = copy.First_Editor || ctx.u; copy.First_At = copy.First_At || now; copy.User_Name = ctx.u; copy.ts = now; } INV.set(copy.Invoice_ID, copy); putInv(copy); ch++; } }
    for (const r of news) { const id = String(r.Invoice_ID == null ? '' : r.Invoice_ID).trim(); if (!id || INV.has(id)) continue; const o = newInv(id, r); const ef = {}; for (const k of EDITABLE) if (k in r) ef[k] = r[k]; applyFields(o, ef, now, { u: '' }, { keepReceived: true, lenient: true }); if (o.ts === now) { o.First_Editor = ''; o.User_Name = ''; o.ts = 0; o.First_At = 0; } INV.set(id, o); putInv(o); nw++; }
    for (const id of remove) if (INV.delete(id)) { invVer++; Q('DELETE FROM invoices WHERE id=?').run(id); rm++; }
  });
  broadcast('reload', { src: req.headers['x-client'] || '' }); return [200, { changed: ch, added: nw, removed: rm }];
});
route('POST', /^\/api\/invoices\/delete-all$/, async (req, res, ctx, b) => {
  adminOnly(ctx); if (b.confirm !== 'حذف') throw bad('اكتب كلمة التأكيد'); await saveBackup('قبل حذف كل الفواتير', ctx.u);
  tx(() => { Q('DELETE FROM invoices').run(); INV.clear(); invVer++; }); broadcast('reload', { src: req.headers['x-client'] || '' }); return [200, { ok: true }];
});
route('PUT', /^\/api\/lookups$/, async (req, res, ctx, b) => {
  need(ctx, 'lookups'); const clean = (a, ks) => (Array.isArray(a) ? a : []).map(x => Object.fromEntries(ks.map(k => [k, String(x && x[k] != null ? x[k] : '').trim().slice(0, 200)]))).filter(x => x[ks[0]]);
  const WH = clean(b.WH, ['code', 'name']), DR = clean(b.DR, ['name', 'loc']); kvSet('WH', WH); kvSet('DR', DR);
  broadcast('lookups', { WH, DR, src: req.headers['x-client'] || '' }); return [200, { ok: true }];
});
/* المستخدمون (للمدير) */
route('GET', /^\/api\/users$/, async (req, res, ctx) => { adminOnly(ctx); return [200, { users: Q('SELECT * FROM users ORDER BY username').all().map(x => ({ ...pub(x), phone: x.phone || '' })) }]; });
route('POST', /^\/api\/users$/, async (req, res, ctx, b) => { adminOnly(ctx); await addUser(b.username, b.password, b.role, true, b.phone); broadcast('users', {}, c => c.role === 'admin'); return [200, { ok: true }]; });
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
  if ('phone' in b) Q('UPDATE users SET phone=? WHERE username=?').run(String(b.phone || '').trim().slice(0, 30) || null, name);
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
route('POST', /^\/api\/backups$/, async (req, res, ctx, b) => { need(ctx, 'backup'); const at = await saveBackup('يدوية', ctx.u); kvSet('bkset', { ...kvGet('bkset', {}), lastSnap: at }); return [200, { at }]; });
route('GET', /^\/api\/backups\/(.+)\/file$/, async (req, res, ctx, b, m) => {
  need(ctx, 'backup'); const at = decodeURIComponent(m[1]), r = Q('SELECT blob FROM backups WHERE at=?').get(at); if (!r) throw new HttpError(404, 'النسخة غير موجودة');
  if (ctx.role === 'admin' && /\bgzip\b/.test(req.headers['accept-encoding'] || '')) { res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Content-Encoding': 'gzip', 'Cache-Control': 'no-store', 'Content-Disposition': `attachment; filename="${bkName()}"` }); res.end(Buffer.from(r.blob)); return null; }
  const d = JSON.parse(zlib.gunzipSync(Buffer.from(r.blob)).toString()); d.items = d.invs; await streamBackup(req, res, d, ctx.role !== 'admin', bkName()); return null;
});
route('GET', /^\/api\/backup-now$/, async (req, res, ctx) => { need(ctx, 'backup'); await streamBackup(req, res, dBase(), ctx.role !== 'admin', bkName()); return null; });
route('GET', /^\/api\/invoices$/, async (req, res, ctx) => { const buf = await invoicesGz(); res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Content-Encoding': 'gzip', 'Cache-Control': 'no-store' }); res.end(buf); return null; });
route('POST', /^\/api\/backups\/(.+)\/restore$/, async (req, res, ctx, b, m) => { const at = decodeURIComponent(m[1]); await restore(loadBackup(at), ctx, new Date(at).toISOString(), req.headers['x-client'] || '', true); return [200, { ok: true }]; });
route('POST', /^\/api\/restore-file$/, async (req, res, ctx, b) => { await restore(b.data, ctx, 'ملف', req.headers['x-client'] || ''); return [200, { ok: true }]; });
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
      const open = r.re.source.includes('login') || r.re.source.includes('logout') || r.re.source.includes('forgot') || r.re.source.includes('api\\/me');
      if (!ctx && !open) throw new HttpError(401, 'سجّل الدخول أولاً');
      if (ctx && ctx.mustChange && !(r.re.source.includes('password') || r.re.source.includes('logout') || r.re.source.includes('forgot') || r.re.source.includes('api\\/me'))) throw new HttpError(403, 'يجب تغيير كلمة المرور أولاً');
      if (req.method !== 'GET' && !req.headers['x-requested-with']) throw new HttpError(403, 'طلب غير مسموح');
      const body = ['POST', 'PUT', 'DELETE'].includes(req.method) ? await readBody(req) : {};
      const out = await r.fn(req, res, ctx, body, p.match(r.re));
      if (out === null) return; const [st, obj, hd] = out;
      if (req.method !== 'GET' && !/\/(login|logout)$/.test(p)) markDirty();
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
  bootstrap().then(() => {
    server.listen(PORT, HOST, () => console.log(`خادم أذون الفواتير يعمل على http://localhost:${PORT}  (البيانات: ${DATA_DIR})${syncOn() ? '  — الحفظ الخارجي المشفّر: مُفعّل' : ''}`));
    setTimeout(bkTick, 2000).unref(); setInterval(bkTick, 60000).unref(); keepAlive();
    if (storageWarn()) console.warn('\n⚠ تحذير: السيرفر يعمل على Render بدون قرص دائم ولا حفظ خارجي — ستُفقد البيانات عند إعادة التشغيل. راجع README-AR.md.\n');
  }).catch(e => { console.error('فشل الإقلاع:', e.message); process.exit(1); });
  const stop = async () => { try { await Promise.race([doSync(), new Promise(r => setTimeout(r, 8000))]); } catch (_) {} try { db.exec('PRAGMA wal_checkpoint(TRUNCATE)'); } catch (_) {} process.exit(0); }; process.on('SIGINT', stop); process.on('SIGTERM', stop);
}
module.exports = { server, awsSign, encBuf, decBuf };
