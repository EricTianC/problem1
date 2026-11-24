import { readFile } from 'node:fs/promises';
import { createServer } from 'node:http';

const routes = new Map([
  ['/', ['site/index.html', 'text/html']],
  ['/style.css', ['site/style.css', 'text/css']],
  ['/app.js', ['site/app.js', 'text/javascript']],
  ['/tasks.json', ['site/tasks.json', 'application/json']],
  ...['AGENTS.md', 'Problem1/Statement.lean', 'Problem1/Starter.lean', 'attempts/README.md']
    .map((path) => [`/${path}`, [path, 'text/plain']]),
]);

createServer(async (req, res) => {
  if (req.url === '/deployment.json') {
    res.writeHead(200, { 'Content-Type': 'application/json' }).end('null');
    return;
  }
  const route = routes.get(req.url);
  if (!route) {
    res.writeHead(404).end();
    return;
  }
  const [file, mime] = route;
  try {
    const data = await readFile(new URL(`../${file}`, import.meta.url));
    res.writeHead(200, { 'Content-Type': `${mime}; charset=utf-8` }).end(data);
  } catch (error) {
    console.error(error);
    res.writeHead(500).end();
  }
}).listen(4173, 'localhost', () => console.log('预览：http://localhost:4173'));
