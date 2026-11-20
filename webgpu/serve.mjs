#!/usr/bin/env node
// A static server for the worked example.  WebGPU needs a secure context; localhost is
// one, so `http://127.0.0.1:PORT/` works in a browser (file:// does not).
//
//   node webgpu/serve.mjs [PORT]        (default 8080, 0 picks a free port)
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { existsSync, statSync } from 'node:fs';
import { dirname, extname, join, normalize, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const types = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.wgsl': 'text/plain; charset=utf-8',
  '.wiz': 'text/plain; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
};

export function startServer(root = here, port = 0) {
  const base = resolve(root);
  const server = createServer(async (req, res) => {
    try {
      const url = new URL(req.url, 'http://localhost');
      let path = normalize(decodeURIComponent(url.pathname)).replace(/^(\.\.[/\\])+/, '');
      if (path === '/' || path === '\\') path = '/index.html';
      const file = resolve(join(base, path));
      if (!file.startsWith(base + '/') && file !== base) { res.writeHead(403).end('forbidden'); return; }
      if (!existsSync(file) || statSync(file).isDirectory()) { res.writeHead(404).end('not found'); return; }
      const body = await readFile(file);
      res.writeHead(200, { 'content-type': types[extname(file)] || 'application/octet-stream' });
      res.end(body);
    } catch (e) {
      res.writeHead(500).end(String(e));
    }
  });
  return new Promise((ok) => server.listen(port, '127.0.0.1', () => ok(server)));
}

if (import.meta.main) {
  const port = Number(process.argv[2] || 8080);
  const server = await startServer(here, port);
  console.log(`serving webgpu/ at http://127.0.0.1:${server.address().port}/`);
}
