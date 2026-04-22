# Vertica Navigator

[![Python](https://img.shields.io/badge/python-3.8%2B-blue.svg)](https://www.python.org/)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](#license)
[![Status](https://img.shields.io/badge/status-stable-brightgreen.svg)]()

**Vertica Navigator** is a self-contained, browser-based SQL workspace and query profiler for the [Vertica Analytic Database](https://www.vertica.com/). It turns the raw output of Vertica's `PROFILE` statement and its ~30 system tables (`v_monitor.*`, `v_internal.*`, `v_catalog.*`) into a set of visual, clickable diagnostic views — without leaving the browser.

A single Python file runs the whole thing: HTTPS server, session management, Vertica client, and every UI page are embedded. No framework, no database for application state, no build step.

---

## Table of contents

- [Screenshots / feature tour](#screenshots--feature-tour)
- [Features](#features)
- [Quick start](#quick-start)
- [Installation](#installation)
- [Configuration](#configuration)
  - [Credentials file](#credentials-file)
  - [Environment variables](#environment-variables)
  - [TLS / HTTPS](#tls--https)
- [Architecture](#architecture)
- [Security model](#security-model)
- [Operations](#operations)
- [Required Vertica privileges](#required-vertica-privileges)
- [Troubleshooting](#troubleshooting)
- [Development](#development)
- [Author](#author)
- [License](#license)

---

## Screenshots / feature tour

A guided walk through the UI, from first login to the deepest diagnostic view.

### 1. Login page

<img width="3840" height="2095" alt="01-login" src="https://github.com/user-attachments/assets/c4e056c3-0dde-4c97-84b8-7cf8b87218a7" />

The entry point. No local user database — each sign-in opens a real Vertica connection under the end-user's own credentials. The right-hand marketing panel is just a friendly intro; the left-hand form is where the work happens.

### 2. Login with credentials

<img width="2000" height="1091" alt="02-login-filled" src="https://github.com/user-attachments/assets/3791fd39-5073-4f1e-b65e-2020109c520d" />

Enter any valid Vertica username and password. Vertica does the authentication; Vertica Navigator only proxies it. Session credentials are kept encrypted in memory (Fernet / AES-128-CBC + HMAC-SHA-256) for the life of the session and never written to disk.

### 3. Database Navigator — query on a table

<img width="3840" height="2095" alt="03-navigator-query" src="https://github.com/user-attachments/assets/e15f5f18-8422-4386-aa37-45d56e432640" />


The main workspace after signing in. The left panel is a filterable tree of schemas, tables, columns, and views, built from `v_catalog`. Check a table in the tree and press **Generate Query** to populate the editor with a `SELECT * FROM schema.table LIMIT 100;` scaffold, then run it — results appear in a tab below the editor with execution time.

### 4. SQL Beautifier

<img width="2000" height="1091" alt="04-beautified-sql" src="https://github.com/user-attachments/assets/d3117c09-fd98-47c9-add7-0e9e7e7826cf" />


Paste any query (messy or minified) and click **Beautify**. A server-side tokenizer normalizes keyword casing, breaks the SELECT list onto separate lines, aligns `JOIN … ON`, stacks conjunctions, and indents subqueries / CASE expressions. Reformatting an already-formatted statement is idempotent — no drift between runs.

### 5. Tabbed query results

<img width="2000" height="1091" alt="05-query-results" src="https://github.com/user-attachments/assets/a40b3993-fcb2-4b08-9687-fea69e87a2ce" />


Every `Run Queries` call opens its own tab with the execution time, a scrollable result grid, and close buttons per tab. Errors land in their own tab so they never blow away a good result set.

### 6. Profile tab — textual profile with dynamic findings

<img width="2000" height="1091" alt="06-profile-text" src="https://github.com/user-attachments/assets/296b905a-a013-40e1-90ea-94d73583a8b5" />


Select a single statement and click **Profile** to run it under Vertica's `PROFILE` wrapper and collect the full set of diagnostic artefacts from `v_monitor` and `v_internal`. The header line summarises the run (Duration, Plan Steps, Good / Warning / Bad counts) and the three links below jump to the **Graphical Profile**, **Skew Between Nodes**, and **ScoreCard** views. Underneath, a plain-English findings list explains what the optimizer did and why — slowest path, event triggers, node skew, and concrete remediation for each.

### 7. Graphical Query Execution Tree

<img width="2000" height="1091" alt="07-graphical-profile" src="https://github.com/user-attachments/assets/e3f29050-8b7a-4f4f-9aae-1a9bf3bf83fd" />


The same query, rendered as a branching tree of cards — one per `path_id` — with coloured edges that reflect data flow (gray = local, orange dashed = resegment, purple dashed = broadcast). Click any card to open a popup with **Performance**, **Estimates**, **Execution** (per-node breakdown), **Details**, **Operators**, and **Query Events** sections. Card colour is an advisory: red means "start here," orange means "investigate," blue / green are fine.

### 8. Help overlay — "How to read this tree"

<img width="2000" height="1091" alt="08-tree-help-overlay" src="https://github.com/user-attachments/assets/2a3c9c7f-9e62-4ed7-bf3c-1af4e6f4482d" />


Every page has `?` help chips that open a plain-English explanation. The tree-overview chip adds a **dynamic** "About this specific query" section: observations computed server-side from the actual profile (tree shape, slowest path with share of wall-clock, spill events, resegment events, per-node timing skew, projection suggestions) — all offline, no LLM, no network calls.

### 9. Card detail popup

<img width="2000" height="1091" alt="09-card-details-popup" src="https://github.com/user-attachments/assets/4046bb09-eaa3-44e3-82d1-82c1478343b3" />


Clicking a card opens its detail popup anchored to the cursor. The popup shows a **status banner** explaining why the card got its colour (here: MODERATE — "No bad query events; time is 0% of the slowest card"), followed by every metric the path produced: percentage of query, exec time, clock time, rows processed, memory, cost, and estimates vs. actuals.

### 10. Formula / source-SQL overlay

<img width="3840" height="2095" alt="10-formula-chip-overlay" src="https://github.com/user-attachments/assets/6b9d07fc-c694-4032-93c0-9da93884a43d" />


Every value on the graph page has a small `ⓘ` chip next to it. Clicking the chip opens this overlay showing the exact SQL used to produce that number and the Python formula that post-processed it. This lets a DBA cross-check every displayed value against the system tables — nothing is opaque.

### 11. Skew Between Nodes — chart view

<img width="2000" height="1091" alt="11-skew-chart" src="https://github.com/user-attachments/assets/8f67127e-8768-4063-bad0-f2e840fada5a" />


Ranks every distributed execution step by the time gap between the fastest and slowest node. At the top: the slowest step (`CompilePlan:EEpreexecute` here — 24.75 s skew), the node that lagged (`v_eevdb_node0003`), and the per-step bar chart. Toggle between **Skew view** (dispatch imbalance) and **Duration view** (work per node). Ctrl+wheel or the `+ / –` buttons zoom; click and drag to pan.

### 12. Skew popup — per-node breakdown

<img width="2000" height="1091" alt="12-skew-popup" src="https://github.com/user-attachments/assets/5604b05c-5c2f-4c4c-a9c7-75a9f10285dc" />


Click a bar to open this popup. It names the slowest-to-finish node, the first-to-finish node, start-time skew, completion skew, longest per-node duration, and every retry attempt with its timestamp. The three dimensions (start skew, duration, completion skew) let you separate dispatch problems from data-plane problems.

### 13. Query Scorecard — priority filters

<img width="2000" height="1091" alt="13-scorecard-collapsed" src="https://github.com/user-attachments/assets/b56ae89b-aa44-4592-810f-16a45d05697b" />


A rule-based grading of the query against ~30 diagnostic checks. The top bar shows the counts per severity (HIGH 9, MEDIUM 3, LOW 0, OK 12, INFO 6) — click a pill to filter. The body collapses same-severity findings into a single row by default; the finger cue invites a click to expand.

### 14. Query Scorecard — expanded findings

<img width="3840" height="2095" alt="14-scorecard-expanded" src="https://github.com/user-attachments/assets/545d3110-e91c-42d8-86b3-3c43e240c641" />

The expanded view. Each row is a single check: **severity**, **type** (GROUPBY / NETWORK / STATS / CPU / SKEW / EVENT), a short **finding** line, a **description**, a **recommended action** (what to change — often with copy-pasteable SQL), and the **measured value** that tripped the check. The underlying SQL runs inside session-private `LOCAL TEMPORARY` tables so it never interferes with other sessions.

---

## Features

### Browser SQL workspace

- Schema / table / view tree populated from `v_catalog` on login.
- Editor with client-side SQL syntax highlighting (no external JS libraries beyond what the page inlines).
- **Server-side beautifier** (`/api/beautify_sql`) — a full tokenizer that handles SELECT-lists, JOINs, ON-clauses, WHERE conjunctions, CASE, subqueries, function calls, string literals, and both comment styles. Reformatting a formatted statement is idempotent.
- Right-click a tree node to insert a fully-qualified identifier at the cursor.
- Tabs for each result set; errors land in their own tab.

### Profiling workflow

Submitting a query from the **Profile** tab runs:

1. `PROFILE <your query>` in a fresh Vertica cursor.
2. Location of `transaction_id` / `statement_id` via `query_requests`.
3. A series of `SELECT`s against `dc_explain_plans`, `query_plan_profiles`, `execution_engine_profiles`, `query_events`, `dc_query_executions`, `projection_usage`, `projection_columns`, `dc_lock_attempts`, `resource_acquisitions`, etc. — organised as numbered "steps" in the output text.
4. A pass that builds a structured `graph_data` object (nodes + edges + summary + findings) consumed by the graph page.
5. In-memory storage of the profile run, keyed by a random `profile_id`, with a 12 h TTL.

### Graphical profile

- One card per `path_id` in the plan, positioned by the outer / inner + depth topology inferred from the plan text.
- Status colour per card: **Fast / Moderate / Slow / Critical**, assigned cross-card so large plans don't go all-red.
- Edge labels derived from the plan: outer / inner, hash / merge, local / broadcast / resegment, plus a plain-language glossary behind the `?` chip.
- Popup per card with **Performance**, **Estimates**, **Execution**, **Details**, **Operators**, and **Query Events** sections.
- **`?` chips** next to every value open a plain-English explanation; **`ⓘ` chips** show the exact SQL / formula used to compute the value.
- **Dynamic findings** computed offline from profile data: slowest-path, spill events, resegment-many-rows events, no-histogram warnings, auto-projection usage, per-node skew, big scans, join dominance, retention knob suggestions.

### Cross-node skew view

- For each distributed execution step in `dc_query_executions`, ranks by **start skew** (dispatch imbalance) and **duration** (work per node).
- Click a bar for a popup that names the slowest-to-finish node, per-node offsets, and per-node durations.
- Flip between Skew view and Duration view; zoom and pan with mouse, keyboard, or Ctrl+wheel.

### Query Scorecard

- ~30 diagnostic checks organised by category (PLAN / STATS / CPU / SKEW / RESOURCES / EVENTS / PHASE / PROJECTION).
- Each finding has a **severity** (HIGH / MEDIUM / LOW / OK / INFO), a **measured value**, a **description**, and a **recommended action** — filterable by severity.
- Runs in session-private `LOCAL TEMPORARY` tables so it never interferes with other sessions.

### Operational niceties

- Activity status bar at the bottom of every page tracks in-flight `fetch()` calls.
- Scanner-noise suppression in the access log drops probes for `/etc/passwd`, `phpinfo.php`, `jmx-console`, and ~40 other common attack paths.
- Graceful handling of client disconnects (no `BrokenPipeError` tracebacks in the log when a user closes a tab mid-profile).
- A 301 redirect listener on the HTTP port sends everything to HTTPS when TLS is enabled.
- Transaction / statement IDs are sent to the browser as strings because they can exceed `Number.MAX_SAFE_INTEGER` and `JSON.parse` would otherwise round.

---

## Quick start

```bash
# 1. Install dependencies
sudo python3 -m pip install vertica-python cryptography

# 2. Drop a credentials file next to the script
mkdir -p ASSETS
cat > ASSETS/vertica_credentials.json <<'EOF'
{
    "host": "vertica.example.com",
    "port": 5433,
    "database": "mydb",
    "tlsmode": "disable"
}
EOF

# 3. Start the server
python3 1_1_vertica_navigator.py

# 4. Open https://<your-host>:8443/ in a browser and sign in.
```

On first start with HTTPS enabled and no cert files present, a self-signed certificate is generated automatically into `ASSETS/generated_tls/`.

---

## Installation

Requirements:

- Python **3.8 or newer**
- `vertica-python` — Vertica's official Python client
- `cryptography` — for in-memory session-credential encryption and for auto-generating self-signed TLS certs

On RHEL / Alma / Rocky:

```bash
sudo dnf install -y python3 python3-pip
sudo python3 -m pip install vertica-python cryptography
```

On Ubuntu / Debian:

```bash
sudo apt-get install -y python3 python3-pip
sudo python3 -m pip install vertica-python cryptography
```

---

## Configuration

### Credentials file

A JSON file describing **how to connect to Vertica** — not end-user credentials. Searched in this order:

1. `./ASSETS/vertica_credentials.json` *(preferred — keeps the repo root tidy)*
2. `./vertica_credentials.json`
3. `/mnt/data/vertica_credentials.json`

Minimum contents:

```json
{
    "host": "vertica.example.com",
    "port": 5433,
    "database": "mydb",
    "tlsmode": "disable"
}
```

Any additional keys the `vertica-python` client accepts (`connection_timeout`, `tlsmode`, `backup_server_node`, ...) can be added to this file and will be merged into the connection info at login time.

**End-user `user` and `password` are intentionally NOT in this file.** Each end-user signs in through the login page with their own Vertica credentials. Vertica does all the authentication — Vertica Navigator simply proxies it.

### Environment variables

All optional.

| Variable | Default | Purpose |
|---|---|---|
| `VERTICA_NAVIGATOR_HOST` | `0.0.0.0` | Bind address. |
| `VERTICA_NAVIGATOR_PUBLIC_HOST` | *(auto-detect)* | Host shown in the startup banner and 301 redirect. Useful when the server runs behind a load balancer. |
| `VERTICA_NAVIGATOR_HTTP_PORT` | `8001` | HTTP port. When HTTPS is enabled this port serves 301 redirects only. |
| `VERTICA_NAVIGATOR_HTTPS_PORT` | `8443` | HTTPS port. |
| `VERTICA_NAVIGATOR_HTTPS_ENABLED` | `1` | Set to `0` to run plain HTTP only. |
| `VERTICA_NAVIGATOR_HTTP_REDIRECT_TO_HTTPS` | `1` | Set to `0` to disable the HTTP → HTTPS redirect listener. |
| `VERTICA_NAVIGATOR_SSL_CERTFILE` | `ASSETS/generated_tls/server.crt` | PEM certificate. |
| `VERTICA_NAVIGATOR_SSL_KEYFILE` | `ASSETS/generated_tls/server.key` | PEM private key. |
| `VERTICA_NAVIGATOR_TLS_DIR` | `ASSETS/generated_tls` | Where auto-generated certificates are written. |
| `VERTICA_NAVIGATOR_TLS_VALID_DAYS` | `365` | Validity of auto-generated certificates. |
| `VERTICA_NAVIGATOR_QPROF_SCRIPT` | *(auto-locate)* | Path to the optional `qprof.sh` helper. |
| `VERTICA_NAVIGATOR_QPROF_TEMP_ROOT` | `$TMPDIR/vertica_navigator_qprof` | Scratch directory for per-session temp files. |

### TLS / HTTPS

- **Default behaviour**: HTTPS on port 8443 with a self-signed certificate generated on first start. Port 8001 redirects to port 8443.
- **Browser warning**: self-signed certificates trigger a one-time "Not secure" warning. Trust the cert in your OS / browser keychain to suppress it.
- **Production deployments** should supply an organisation-issued certificate via `VERTICA_NAVIGATOR_SSL_CERTFILE` / `_SSL_KEYFILE`.
- **Plain HTTP** is supported (`VERTICA_NAVIGATOR_HTTPS_ENABLED=0`), but passwords cross the wire in the clear — use it only on localhost or inside a mesh that already encrypts in-transit traffic.

---

## Architecture

```
  Browser
    │   HTTPS
    ▼
  ┌─────────────────────────────────────────────────────┐
  │ 1_1_vertica_navigator.py  (single Python process)    │
  │                                                      │
  │   ThreadingHTTPServer ── DBTreeHandler               │
  │             │                                        │
  │             ├─ Routes:                               │
  │             │    /               login page          │
  │             │    /app            SQL workspace       │
  │             │    /profile/*      graphical profile   │
  │             │    /skew/*         cross-node skew     │
  │             │    /scorecard/*    query scorecard     │
  │             │    /api/*          JSON backend        │
  │             │    /ASSETS/*       static files        │
  │             │                                        │
  │             └─ In-memory state (per process):        │
  │                    SESSIONS          (12 h TTL)      │
  │                    PROFILE_RUNS      (12 h TTL)      │
  │                                                      │
  │   Every request opens a SHORT-LIVED vertica-python    │
  │   connection using the session user's credentials,    │
  │   runs the necessary queries, and closes.             │
  └─────────────────────┬─────────────────────────────────┘
                        │
                        ▼
                Vertica cluster
```

All application state is in memory. Restarting the process drops every active session and every cached profile — by design, as there is no way to recover encrypted session credentials after the process dies.

The UI is server-rendered HTML with all CSS and JavaScript inlined. There is no bundler, no runtime JS framework, and no separate SPA build — the only external runtime dependencies the browser pulls in are ECharts (for the skew chart) and Inter (for typography), both from a CDN.

---

## Security model

| Concern | Mitigation |
|---|---|
| **Authentication** | Vertica authenticates the user at login (`test_login` opens a real connection). Vertica Navigator stores no password database. |
| **Password at rest** | Credentials are never written to disk. |
| **Password in memory** | Username + password are encrypted with a process-lifetime Fernet key (`AES-128-CBC + HMAC-SHA-256`) as soon as they leave the login handler. They are decrypted only at the moment a `vertica_python.connect(...)` call is about to be made and cleared from locals immediately after. |
| **Key lifecycle** | The Fernet key is generated by `os.urandom()` on process start and held only in a module-level variable. It never touches disk. Killing the process invalidates every session. |
| **Session cookie** | Server-side sessions with a random UUID; the cookie carries only the session ID. `HttpOnly`; `Secure` is set when TLS is active. 12 h absolute lifetime, sliding on each request. |
| **CSRF** | The app uses same-origin `fetch` and standard session cookies; no third-party embedding is assumed. |
| **Query execution** | Every SQL statement runs with **the signed-in user's privileges**. Vertica is the authority — Vertica Navigator cannot escalate privileges. A 403-style popup guides users who hit a privilege wall on a `v_monitor` read. |
| **Transport** | HTTPS by default; HTTP redirects to HTTPS when TLS is enabled. |
| **Log hygiene** | Passwords are never logged. Usernames are logged at INFO level. Scanner noise (`../`, `<script>`, `.php`, `jmx-console`, etc.) is suppressed from the access log. |

---

## Operations

### Logs

Written to:

- `vertica_navigator.log` in the working directory (rotated by you, if you like — the app uses a plain `FileHandler`).
- `stdout` (for use with `systemd` / `journalctl`).

Level is **INFO** by default. Set `DEBUG_LOGGING = False` at the top of the file to drop everything but errors.

### Session lifetime

- Absolute: **12 hours** from login.
- Sliding: each request updates `last_seen`; after 12 h of inactivity the session is garbage-collected on the next request.
- A `GET /api/logout` clears the session immediately.

### Multi-user

`ThreadingHTTPServer` serves one thread per request. Session and profile state are protected by `threading.RLock()`. Profile payloads are deep-copied on store / read so concurrent users cannot mutate each other's in-memory data.

### Reverse proxy / load balancer

Set `VERTICA_NAVIGATOR_PUBLIC_HOST` to the externally-visible hostname. Pin sessions to a single backend (the session store is per-process; any sticky-session scheme works — a cookie-based one is easiest since the cookie name is stable).

---

## Required Vertica privileges

A standard Vertica user can sign in, browse their accessible schemas, run their own queries, and profile them. The profiler reads from:

- `v_monitor.query_profiles`, `v_monitor.query_plan_profiles`, `v_monitor.execution_engine_profiles`, `v_monitor.query_events`, `v_monitor.projection_usage`, `v_monitor.resource_acquisitions`, `v_monitor.host_resources`
- `v_internal.dc_explain_plans`, `v_internal.dc_query_executions`, `v_internal.dc_lock_attempts`
- `v_catalog.projections`, `v_catalog.projection_columns`, `v_catalog.nodes`

If the signed-in user is not a superuser, most of those require elevated privileges. When a request hits a privilege wall, the server returns a structured 403 that the frontend renders as a popup with two resolution paths:

1. **Sign in as `dbadmin`** (or any account with `PSEUDOSUPERUSER`).
2. **Ask a DBA to delegate the role** — the popup includes copy-paste `GRANT` + `SET ROLE` SQL.

---

## Troubleshooting

### "Could not find `vertica_credentials.json`"
Create it at one of the three paths listed under [Credentials file](#credentials-file).

### HTTPS startup warning about `cryptography`
Install it (`pip install cryptography`) or disable HTTPS (`VERTICA_NAVIGATOR_HTTPS_ENABLED=0`). Without `cryptography`, certificates cannot be auto-generated and in-memory session encryption falls back to a weaker fallback.

### Every card is orange / red
The cross-card status rules reserve orange and red for cards the user has a concrete reason to focus on. If *every* card is flagged, check whether the profiled query triggered a cluster-wide event (e.g. `GROUP_BY_SPILLED` on every node). Hover over a card's status reason for the exact trigger.

### "No profile data" on every card
`v_monitor.execution_engine_profiles` is per-node and replicates asynchronously; on fast queries the profile collection can outrun the replication window. The server falls back to `query_plan_profiles.running_time` (cluster-wide, always reliable) and marks the value `(plan)` on the card. A DBA can widen Data Collector retention:

```sql
SELECT SET_DATA_COLLECTOR_POLICY('ExecutionEngineProfiles', '86400', '256m');
-- 24 h retention, 256 MB cap
```

### Transaction ID displays differently on the graph page and the text tab
Fixed — transaction IDs are sent to the browser as strings because they can exceed `Number.MAX_SAFE_INTEGER`.

---

## Development

The whole app is one file. To work on it:

```bash
# Run directly
python3 1_1_vertica_navigator.py

# Lint
python3 -m pyflakes 1_1_vertica_navigator.py

# Syntax sanity
python3 -c "import py_compile; py_compile.compile('1_1_vertica_navigator.py', doraise=True)"
```

The HTML / CSS / JS for each page is stored as a Python raw-string constant (`LOGIN_HTML`, `APP_HTML`, `PROFILE_HTML`, `SKEW_HTML`, `SCORECARD_HTML`). Templating is plain `str.replace(...)` of a few well-known placeholders — no Jinja, no Mustache. This keeps the file single-file-deployable.

Pull requests welcome. If a change touches a page, update the corresponding docstring and the relevant `HELP_REGISTRY` entry so the `?` chip stays accurate.

---

## Author

**Maya Goldberg** — original author and designer of Vertica Navigator.

The footer of every page inside the application carries the same attribution:

> *This program is provided 'as is' without warranty of any kind. Users assume all risks associated with its use. A valid Vertica product license is required for Vertica usage. Created by Maya Goldberg.*

## Acknowledgements

- [Vertica](https://www.vertica.com/) for the database and the extensive system-table documentation that makes a tool like this possible. Vertica is a trademark of Open Text Corporation; this project is neither endorsed by nor affiliated with Open Text.
- [ECharts](https://echarts.apache.org/) for the skew-view charts.
- [Inter](https://rsms.me/inter/) for typography.

---

## License

Released under the **MIT License**.

```
MIT License

Copyright (c) 2026 Maya Goldberg

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

A copy of this text is also provided as a separate `LICENSE` file at the repository root.
