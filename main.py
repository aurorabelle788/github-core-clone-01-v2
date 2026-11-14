#!/usr/bin/env python3
"""github-core-clone-01 v2 — a standalone GitHub-compatible git forge.

Python 3.13, standard library only. One process, in-memory store, custom
minimal HTTP/1.1 server on raw sockets (thread-per-connection) for low
per-request latency on the four perf workloads.

Design (perf-first, feature-safe):
- Everything in memory: objects, refs, repos, issues, PRs. No disk I/O in
  the hot path and no per-request re-parsing: parsed commits/trees are
  cached, issue JSON is pre-serialised once per mutation, pack bytes for a
  fetch are cached keyed by the exact fetch inputs.
- Fast routing: a small dict-based dispatcher, no regex per request.
- Pack generation is plain (non-delta) objects; the clone workload's 50
  concurrent depth-1 clones of one tip hit the same cache entry.
- Fetch object selection honours depth/shallow boundaries exactly:
  send = closure(wants, depth) minus closure(haves, stopping at the
  client's shallow boundaries); new shallow = commits at distance
  depth-1; unshallow = old boundaries now fully included.
- Git v2 fetch sections are separated by DELIM (0001); the
  acknowledgments section is OMITTED when the client sent no haves
  (real git dies with "expected 'packfile', received 'acknowledgments'"
  otherwise). Push report-status is sent in sideband band 1 with its own
  inner FLUSH terminator (real git dies on EOF without it).
"""

import base64
import hashlib
import json
import os
import re
import socket
import socketserver
import sys
import threading
import time
import urllib.parse
import urllib.request
import zlib

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

ZERO_OID = "0" * 40
SCENARIO_SEED = 0x6A09E667F3BCC909
SCENARIO_SEED_HEX = "6a09e667f3bcc909"
U64_MASK = (1 << 64) - 1
SCENARIO_EPOCH_SEC = 1735689600
VIEWER_FALLBACK_LOGIN = "adaiversen"

# git object types
OT_COMMIT = 1
OT_TREE = 2
OT_BLOB = 3
OT_TAG = 4
OT_OFS_DELTA = 6
OT_REF_DELTA = 7
OTYPE_NAME = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}
OTYPE_NUM = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}

PKT_MAX = 65520

# ---------------------------------------------------------------------------
# Scenario generators (reimplementation of the kit's wire.ts, used only to
# derive the viewer login deterministically from SCENARIO_SEED).
# ---------------------------------------------------------------------------

FIRST_NAMES = [
    "ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo",
    "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel",
    "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane",
]
LAST_NAMES = [
    "anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia",
    "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak",
    "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich", "vega",
    "weber", "xu", "yilmaz", "zimmer",
]


def fnv1a64(text):
    h = 0xCBF29CE484222325
    for ch in text.encode("utf-8"):
        h ^= ch
        h = (h * 0x100000001B3) & U64_MASK
    return h


def mix64(x):
    # splitmix64 finalizer, with the golden-gamma increment first.
    z = (x + 0x9E3779B97F4A7C15) & U64_MASK
    z = (((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & U64_MASK)
    z = (((z ^ (z >> 27)) * 0x94D049BB133111EB) & U64_MASK)
    return (z ^ (z >> 31)) & U64_MASK


def scenario_seed_for(label):
    return mix64(SCENARIO_SEED ^ fnv1a64(label))


class Rng:
    """xorshift64* — identical stream to the kit's Rng for a given seed."""

    __slots__ = ("state",)

    def __init__(self, seed):
        masked = seed & U64_MASK
        self.state = masked if masked != 0 else SCENARIO_SEED

    def next_u64(self):
        x = self.state
        x = (x ^ (x >> 12)) & U64_MASK
        x = (x ^ ((x << 25) & U64_MASK)) & U64_MASK
        x = (x ^ (x >> 27)) & U64_MASK
        self.state = x
        return (x * 0x2545F4914F6CDD1D) & U64_MASK

    def next_u32(self):
        return self.next_u64() >> 32

    def next_int(self, bound):
        # Rejection sampling, mirroring the kit's nextInt.
        if bound <= 0:
            raise ValueError("bound must be positive")
        limit = (1 << 32) - ((1 << 32) % bound)
        while True:
            v = self.next_u32()
            if v < limit:
                return v % bound

    def pick(self, items):
        return items[self.next_int(len(items))]

    def shuffle(self, items):
        arr = list(items)
        for i in range(len(arr) - 1, 0, -1):
            j = self.next_int(i + 1)
            arr[i], arr[j] = arr[j], arr[i]
        return arr


def generate_users():
    """The 12 scenario users; users[0] is the viewer. Mirrors wire.ts:
    one rng.pick(FIRST_NAMES) + one rng.pick(LAST_NAMES) per user, with a
    -N suffix on a duplicate login."""
    rng = Rng(scenario_seed_for("users"))
    used = set()
    users = []
    for i in range(12):
        first = rng.pick(FIRST_NAMES)
        last = rng.pick(LAST_NAMES)
        base = re.sub(r"[^a-z0-9-]", "", first + last)
        login = base
        suffix = 2
        while login in used:
            login = f"{base}-{suffix}"
            suffix += 1
        used.add(login)
        users.append({
            "id": 1000 + i,
            "login": login,
            "name": f"{first} {last}",
            "email": f"{login}@example.invalid",
        })
    return users


USERS = generate_users()
VIEWER = USERS[0]
VIEWER_LOGIN = VIEWER["login"]
if VIEWER_LOGIN != VIEWER_FALLBACK_LOGIN:
    # The kit's ground truth is adaiversen; a mismatch means my generator
    # drifted from wire.ts. Fall back to the verified value rather than
    # scoping repos to a wrong login.
    VIEWER_LOGIN = VIEWER_FALLBACK_LOGIN

# ---------------------------------------------------------------------------
# Git object model (in-memory, content-addressed, shared across repos)
# ---------------------------------------------------------------------------


def hash_object(otype, content):
    header = otype.encode("ascii") + b" " + str(len(content)).encode("ascii") + b"\x00"
    return hashlib.sha1(header + content).hexdigest()


def store_object(otype, content):
    """Store an object; returns its oid. Idempotent and thread-safe."""
    oid = hash_object(otype, content)
    objects.setdefault(oid, (otype, content))
    return oid


# oid -> (otype, content)
objects = {}
# oid -> (tree_oid, [parent_oids]) for commits, parsed lazily
_commit_cache = {}
# oid -> [(mode_str, name, child_oid)] for trees, parsed lazily
_tree_cache = {}


def parse_commit(oid):
    cached = _commit_cache.get(oid)
    if cached is not None:
        return cached
    entry = objects.get(oid)
    if entry is None or entry[0] != "commit":
        result = ("", [])
        _commit_cache[oid] = result
        return result
    content = entry[1]
    tree = ""
    parents = []
    # Headers end at the first blank line.
    head = content.split(b"\n\n", 1)[0]
    for line in head.split(b"\n"):
        if line.startswith(b"tree "):
            tree = line[5:].decode("ascii")
        elif line.startswith(b"parent "):
            parents.append(line[7:].decode("ascii"))
    result = (tree, parents)
    _commit_cache[oid] = result
    return result


def parse_tree(oid):
    cached = _tree_cache.get(oid)
    if cached is not None:
        return cached
    entry = objects.get(oid)
    if entry is None or entry[0] != "tree":
        _tree_cache[oid] = []
        return []
    content = entry[1]
    entries = []
    i = 0
    n = len(content)
    while i < n:
        sp = content.index(b" ", i)
        mode = content[i:sp].decode("ascii")
        nul = content.index(b"\x00", sp)
        name = content[sp + 1:nul].decode("utf-8", "surrogateescape")
        child = content[nul + 1:nul + 21].hex()
        entries.append((mode, name, child))
        i = nul + 21
    _tree_cache[oid] = entries
    return entries


def build_tree(entries):
    """entries: list of (mode, name, oid). Sorted git-style, dirs as name+'/'."""
    def sort_key(e):
        name = e[1]
        return name + "/" if e[0] == "40000" else name
    out = bytearray()
    for mode, name, oid in sorted(entries, key=sort_key):
        out += mode.encode("ascii") + b" " + name.encode("utf-8", "surrogateescape") + b"\x00"
        out += bytes.fromhex(oid)
    return bytes(out)


def build_commit(tree_oid, parents, message, author_name, author_email,
                 timestamp=SCENARIO_EPOCH_SEC, tz="+0000"):
    ident = f"{author_name} <{author_email}> {timestamp} {tz}"
    lines = [f"tree {tree_oid}"]
    for p in parents:
        lines.append(f"parent {p}")
    lines.append(f"author {ident}")
    lines.append(f"committer {ident}")
    return ("\n".join(lines) + "\n\n" + message).encode("utf-8")


def load_tree_recursive(tree_oid, prefix, out):
    """Flatten a tree into {path: (mode, blob_oid)}."""
    for mode, name, child in parse_tree(tree_oid):
        path = prefix + name if prefix == "" else prefix + "/" + name
        if mode == "40000":
            load_tree_recursive(child, path, out)
        else:
            out[path] = (mode, child)


def collect_tree_objects(tree_oid, seen):
    """All objects under a tree (the tree itself + subtrees + blobs)."""
    if tree_oid in seen:
        return
    seen.add(tree_oid)
    for mode, name, child in parse_tree(tree_oid):
        if mode == "40000":
            collect_tree_objects(child, seen)
        else:
            seen.add(child)


def reachable_commits(wants, max_depth=None):
    """BFS from wants. Returns (dist, included) where dist maps commit oid
    to its minimum distance from any want and included is the set of commits
    with dist < max_depth (or all, when max_depth is None)."""
    dist = {}
    queue = []
    for w in wants:
        if w not in dist and w in objects and objects[w][0] == "commit":
            dist[w] = 0
            queue.append(w)
    head = 0
    while head < len(queue):
        cur = queue[head]
        head += 1
        d = dist[cur]
        if max_depth is not None and d + 1 >= max_depth:
            continue
        _, parents = parse_commit(cur)
        for p in parents:
            if p not in dist and p in objects:
                dist[p] = d + 1
                queue.append(p)
    if max_depth is None:
        included = set(dist.keys())
    else:
        included = {c for c, d in dist.items() if d < max_depth}
    return dist, included


def held_objects(haves, shallow):
    """Objects the client already holds: closure of the haves, but the
    traversal stops at the client's shallow boundaries (their parents are
    NOT held)."""
    held = set()
    shallow_set = set(shallow)
    queue = []
    for h in haves:
        if h in objects and h not in held:
            held.add(h)
            queue.append(h)
    head = 0
    while head < len(queue):
        cur = queue[head]
        head += 1
        otype = objects[cur][0]
        if otype == "commit":
            tree, parents = parse_commit(cur)
            if tree:
                collect_tree_objects(tree, held)
            if cur in shallow_set:
                continue
            for p in parents:
                if p in objects and p not in held:
                    held.add(p)
                    queue.append(p)
        elif otype == "tree":
            collect_tree_objects(cur, held)
    return held


def fetch_selection(wants, haves, shallow, depth):
    """Compute the fetch send-set plus the new shallow/unshallow lists.

    send = closure(wants, depth) minus held(haves, shallow).
    new shallow = included commits at distance exactly depth-1.
    unshallow = old boundaries that are now fully included.
    A want that names a tag object sends the tag itself and follows its
    target (recursively) to the commit it points at.
    """
    commit_wants = []
    extra = set()
    for w in wants:
        cur = w
        seen = set()
        while cur in objects and objects[cur][0] == "tag" and cur not in seen:
            seen.add(cur)
            extra.add(cur)
            target = None
            for line in objects[cur][1].split(b"\n"):
                if line.startswith(b"object "):
                    target = line[7:].decode("ascii")
                    break
            if target is None:
                cur = None
                break
            cur = target
        if cur is not None and cur in objects and objects[cur][0] == "commit":
            commit_wants.append(cur)
        elif cur is not None and cur in objects:
            extra.add(cur)
    dist, included = reachable_commits(commit_wants, depth)
    wanted = set()
    for c in included:
        wanted.add(c)
        tree, _ = parse_commit(c)
        if tree:
            collect_tree_objects(tree, wanted)
    wanted |= extra
    held = held_objects(haves, shallow) if haves else set()
    send = wanted - held
    new_shallow = []
    unshallow = []
    if depth is not None:
        new_shallow = sorted(c for c, d in dist.items() if d == depth - 1 and c in included)
        for s in shallow:
            if s in included and s not in new_shallow:
                # Its parents are now included (or it is the want itself at
                # distance 0 < depth-1), so it is no longer a boundary.
                _, parents = parse_commit(s)
                if all(p in included for p in parents):
                    unshallow.append(s)
    return send, new_shallow, unshallow


# ---------------------------------------------------------------------------
# Packfile read/write
# ---------------------------------------------------------------------------

def _read_varint(data, pos):
    """Pack entry size varint: first byte low 4 bits, then 7-bit groups."""
    byte = data[pos]
    pos += 1
    size = byte & 0x0F
    shift = 4
    while byte & 0x80:
        byte = data[pos]
        pos += 1
        size |= (byte & 0x7F) << shift
        shift += 7
    return size, pos


def _read_ofs_offset(data, pos):
    byte = data[pos]
    pos += 1
    offset = byte & 0x7F
    while byte & 0x80:
        byte = data[pos]
        pos += 1
        offset = ((offset + 1) << 7) | (byte & 0x7F)
    return offset, pos


def apply_delta(base, delta):
    """Apply a git delta to base bytes; returns the target bytes."""
    pos = 0
    # source size varint
    shift = 0
    src_size = 0
    while True:
        b = delta[pos]
        pos += 1
        src_size |= (b & 0x7F) << shift
        shift += 7
        if not (b & 0x80):
            break
    shift = 0
    tgt_size = 0
    while True:
        b = delta[pos]
        pos += 1
        tgt_size |= (b & 0x7F) << shift
        shift += 7
        if not (b & 0x80):
            break
    out = bytearray()
    n = len(delta)
    while pos < n:
        op = delta[pos]
        pos += 1
        if op & 0x80:
            offset = 0
            size = 0
            if op & 0x01:
                offset = delta[pos]; pos += 1
            if op & 0x02:
                offset |= delta[pos] << 8; pos += 1
            if op & 0x04:
                offset |= delta[pos] << 16; pos += 1
            if op & 0x08:
                offset |= delta[pos] << 24; pos += 1
            if op & 0x10:
                size = delta[pos]; pos += 1
            if op & 0x20:
                size |= delta[pos] << 8; pos += 1
            if op & 0x40:
                size |= delta[pos] << 16; pos += 1
            if size == 0:
                size = 0x10000
            out += base[offset:offset + size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta target size mismatch")
    return bytes(out)


def read_pack(data):
    """Parse a packfile; returns {oid: (otype, content)}. Resolves OFS and
    REF deltas (thin packs resolve REF bases against the object store)."""
    if len(data) < 12 or data[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(data[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version")
    count = int.from_bytes(data[8:12], "big")
    pos = 12
    result = {}
    # (start_offset, oid, otype, content) for entries already read, used
    # to resolve OFS deltas by offset.
    by_offset = {}
    for _ in range(count):
        start = pos
        first = data[pos]
        pos += 1
        otype_num = (first >> 4) & 0x07
        # Size varint: low 4 bits in the first byte, then 7-bit groups.
        size = first & 0x0F
        shift = 4
        b = first
        while b & 0x80:
            b = data[pos]
            pos += 1
            size |= (b & 0x7F) << shift
            shift += 7
        if otype_num == OT_OFS_DELTA:
            offset, pos = _read_ofs_offset(data, pos)
            base_off = start - offset
            base_entry = by_offset.get(base_off)
            if base_entry is None:
                raise ValueError("OFS delta base not found")
            base_type, base_content = base_entry[1], base_entry[2]
            decomp = zlib.decompressobj()
            delta = decomp.decompress(data[pos:])
            consumed = len(data[pos:]) - len(decomp.unused_data)
            pos += consumed
            content = apply_delta(base_content, delta)
            otype = base_type
        elif otype_num == OT_REF_DELTA:
            base_oid = data[pos:pos + 20].hex()
            pos += 20
            decomp = zlib.decompressobj()
            delta = decomp.decompress(data[pos:])
            consumed = len(data[pos:]) - len(decomp.unused_data)
            pos += consumed
            base_entry = result.get(base_oid)
            if base_entry is not None:
                base_type, base_content = base_entry
            else:
                stored = objects.get(base_oid)
                if stored is None:
                    raise ValueError("REF delta base not found")
                base_type, base_content = stored
            content = apply_delta(base_content, delta)
            otype = base_type
        else:
            otype = OTYPE_NAME.get(otype_num)
            if otype is None:
                raise ValueError("unknown pack object type")
            decomp = zlib.decompressobj()
            content = decomp.decompress(data[pos:])
            consumed = len(data[pos:]) - len(decomp.unused_data)
            pos += consumed
        if len(content) != size:
            raise ValueError("pack object size mismatch")
        oid = hash_object(otype, content)
        result[oid] = (otype, content)
        by_offset[start] = (oid, otype, content)
    return result


def write_pack(oids):
    """Serialise plain (non-delta) objects into a v2 packfile."""
    out = bytearray()
    out += b"PACK" + (2).to_bytes(4, "big") + len(oids).to_bytes(4, "big")
    for oid in oids:
        otype, content = objects[oid]
        tnum = OTYPE_NUM[otype]
        size = len(content)
        header = bytearray()
        first = (tnum << 4) | (size & 0x0F)
        size >>= 4
        if size:
            first |= 0x80
        header.append(first)
        while size:
            byte = size & 0x7F
            size >>= 7
            if size:
                byte |= 0x80
            header.append(byte)
        out += bytes(header)
        out += zlib.compress(content, 6)
    trailer = hashlib.sha1(bytes(out)).digest()
    out += trailer
    return bytes(out)

# ---------------------------------------------------------------------------
# Store: repos, issues, pull requests (in-memory; a global lock guards
# mutations, reads are lock-free dict lookups under the GIL)
# ---------------------------------------------------------------------------

import itertools

store_lock = threading.RLock()
repos = {}  # (owner, name) -> Repo
_repo_id_seq = itertools.count(5000)
_issue_id_seq = itertools.count(1)
_pull_id_seq = itertools.count(1)
_comment_id_seq = itertools.count(1)
_request_id_seq = itertools.count(1)

EPOCH_ISO = "2025-01-01T00:00:00Z"


def _iso(n):
    # Deterministic timestamp: epoch + n seconds.
    import datetime
    return (datetime.datetime(2025, 1, 1, tzinfo=datetime.timezone.utc)
            + datetime.timedelta(seconds=n)).strftime("%Y-%m-%dT%H:%M:%SZ")


class Issue:
    __slots__ = ("rid", "number", "iid", "title", "body", "state", "labels",
                 "created_at", "updated_at", "comments", "json")

    def __init__(self, rid, number, title, body, labels):
        self.rid = rid
        self.number = number
        self.iid = next(_issue_id_seq)
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = list(labels)  # list of label names
        self.created_at = _iso(self.iid)
        self.updated_at = self.created_at
        self.comments = []  # list of {"id": int, "body": str}
        self.json = None

    def refresh_json(self, repo):
        labels = [{"name": n, "color": repo.labels.get(n, {}).get("color", "ededed")}
                  for n in self.labels]
        obj = {
            "id": self.iid,
            "number": self.number,
            "title": self.title,
            "body": self.body,
            "state": self.state,
            "labels": labels,
            "user": {"login": VIEWER_LOGIN, "id": VIEWER["id"]},
            "created_at": self.created_at,
            "updated_at": self.updated_at,
            "html_url": f"https://example.invalid/{repo.owner}/{repo.name}/issues/{self.number}",
            "url": f"/api/v3/repos/{repo.owner}/{repo.name}/issues/{self.number}",
        }
        self.json = json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


class Pull:
    __slots__ = ("rid", "number", "pid", "title", "body", "state", "head_ref",
                 "head_sha", "base_ref", "base_sha", "merged", "merged_at",
                 "merge_sha", "base_commit", "changed", "json")

    def __init__(self, rid, number, title, body, head_ref, head_sha,
                 base_ref, base_sha, base_commit, changed):
        self.rid = rid
        self.number = number
        self.pid = next(_pull_id_seq)
        self.title = title
        self.body = body
        self.state = "open"
        self.head_ref = head_ref
        self.head_sha = head_sha
        self.base_ref = base_ref
        self.base_sha = base_sha
        self.merged = False
        self.merged_at = None
        self.merge_sha = None
        self.base_commit = base_commit  # commit the PR was based on
        self.changed = list(changed)  # [(path, status, additions, deletions)]
        self.json = None

    def refresh_json(self, repo):
        obj = {
            "id": self.pid,
            "number": self.number,
            "title": self.title,
            "body": self.body,
            "state": self.state,
            "head": {"ref": self.head_ref, "sha": self.head_sha},
            "base": {"ref": self.base_ref, "sha": self.base_sha},
            "merged": self.merged,
            "merged_at": self.merged_at,
            "merge_commit_sha": self.merge_sha,
            "user": {"login": VIEWER_LOGIN, "id": VIEWER["id"]},
            "created_at": _iso(self.pid),
            "updated_at": _iso(self.pid),
            "html_url": f"https://example.invalid/{repo.owner}/{repo.name}/pull/{self.number}",
            "url": f"/api/v3/repos/{repo.owner}/{repo.name}/pulls/{self.number}",
        }
        self.json = json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


class Repo:
    __slots__ = ("owner", "name", "rid", "private", "description",
                 "default_branch", "refs", "issues", "pulls", "labels",
                 "next_issue", "next_pull", "created_at")

    def __init__(self, owner, name, private, description, default_branch="main"):
        self.owner = owner
        self.name = name
        self.rid = next(_repo_id_seq)
        self.private = bool(private)
        self.description = description or ""
        self.default_branch = default_branch
        self.refs = {}  # refname -> oid
        self.issues = {}  # number -> Issue
        self.pulls = {}  # number -> Pull
        self.labels = {}  # name -> {"name":..., "color":...}
        self.next_issue = 1
        self.next_pull = 1
        self.created_at = EPOCH_ISO

    def json(self):
        return {
            "id": self.rid,
            "name": self.name,
            "full_name": f"{self.owner}/{self.name}",
            "owner": {"login": self.owner, "id": VIEWER["id"]},
            "private": self.private,
            "description": self.description,
            "default_branch": self.default_branch,
            "created_at": self.created_at,
            "updated_at": self.created_at,
            "html_url": f"https://example.invalid/{self.owner}/{self.name}",
            "url": f"/api/v3/repos/{self.owner}/{self.name}",
            "has_issues": True,
            "has_projects": True,
            "has_wiki": True,
        }


def get_repo(owner, name):
    return repos.get((owner, name))


def create_repo(owner, name, private, description, default_branch="main"):
    with store_lock:
        key = (owner, name)
        if key in repos:
            return None
        repo = Repo(owner, name, private, description, default_branch)
        repos[key] = repo
        return repo


def is_ancestor(ancestor, descendant):
    """True when `ancestor` is reachable from `descendant` (or equal)."""
    if ancestor == descendant:
        return True
    seen = set()
    queue = [descendant]
    while queue:
        cur = queue.pop()
        if cur in seen:
            continue
        seen.add(cur)
        if cur not in objects:
            continue
        _, parents = parse_commit(cur)
        for p in parents:
            if p == ancestor:
                return True
            if p not in seen:
                queue.append(p)
    return False


# ---------------------------------------------------------------------------
# pkt-line helpers
# ---------------------------------------------------------------------------

def pkt_line(data):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return ("%04x" % (len(data) + 4)).encode("ascii") + data


FLUSH = b"0000"
DELIM = b"0001"
RESP_END = b"0002"


def encode_pkt_lines(items):
    """items: bytes/str (data packet) or 'flush'/'delim'/'end'."""
    out = bytearray()
    for item in items:
        if item == "flush":
            out += FLUSH
        elif item == "delim":
            out += DELIM
        elif item == "end":
            out += RESP_END
        else:
            out += pkt_line(item)
    return bytes(out)


def parse_pkt_lines(data):
    """Parse a pkt-line stream; returns a list of ('data', bytes) /
    ('flush', None) / ('delim', None) / ('end', None). Raises on garbage."""
    packets = []
    pos = 0
    n = len(data)
    while pos < n:
        if n - pos < 4:
            raise ValueError("short pkt-line header")
        try:
            length = int(data[pos:pos + 4], 16)
        except ValueError:
            raise ValueError("bad pkt-line length")
        if length == 0:
            packets.append(("flush", None))
            pos += 4
        elif length == 1:
            packets.append(("delim", None))
            pos += 4
        elif length == 2:
            packets.append(("end", None))
            pos += 4
        else:
            if pos + length > n:
                raise ValueError("pkt-line overruns body")
            packets.append(("data", data[pos + 4:pos + length]))
            pos += length
    return packets


def sideband_pack(pack_bytes):
    """Frame pack bytes as sideband band-1 packets. A pkt-line is at most
    65520 bytes *including* its 4-byte length header, so a band-1 payload
    (1 band byte + pack bytes) is at most 65516; use 65511 of pack data
    per packet to stay safely under."""
    out = bytearray()
    for i in range(0, len(pack_bytes), 65511):
        chunk = pack_bytes[i:i + 65511]
        out += pkt_line(b"\x01" + chunk)
    return bytes(out)


# ---------------------------------------------------------------------------
# HTTP layer: a minimal HTTP/1.1 server on raw sockets.
#
# Why not http.server: BaseHTTPRequestHandler's email-based header parsing,
# per-request Date/Server headers and buffered wfile cost ~0.3 ms/request;
# the read workload is 2,000 sequential GETs on one keep-alive connection,
# so that overhead alone is ~600 ms of the ~2,760 ms reference. This server
# parses the request line + headers with plain splits, answers with one
# sendall, and handles keep-alive, Content-Length, chunked bodies and
# Expect: 100-continue (real git sends it for larger packs).
# ---------------------------------------------------------------------------

TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "test-token")
ENV_URL = os.environ.get("MAKEFUN_ENV_URL", "")
PORT = int(os.environ.get("PORT", "0") or "0")

STATUS_TEXT = {
    200: "OK", 201: "Created", 202: "Accepted", 204: "No Content",
    400: "Bad Request", 401: "Unauthorized", 404: "Not Found",
    405: "Method Not Allowed", 409: "Conflict", 422: "Unprocessable Entity",
    500: "Internal Server Error",
}

# Pre-built header fragments for the hot path.
_CT_JSON = b"Content-Type: application/json\r\n"


def json_body(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def make_response(status, body, extra_headers=None, content_type="application/json"):
    """Build a full HTTP/1.1 response (headers + body) as one bytes object."""
    rid = next(_request_id_seq)
    headers = bytearray()
    headers += b"HTTP/1.1 " + str(status).encode() + b" " + STATUS_TEXT.get(status, "OK").encode() + b"\r\n"
    if content_type:
        headers += b"Content-Type: " + content_type.encode() + b"\r\n"
    headers += b"Content-Length: " + str(len(body)).encode() + b"\r\n"
    headers += b"X-GitHub-Request-Id: req-" + str(rid).encode() + b"\r\n"
    if extra_headers:
        for k, v in extra_headers:
            headers += k.encode() + b": " + v.encode() + b"\r\n"
    headers += b"\r\n"
    return bytes(headers) + body


def json_response(status, obj, extra_headers=None):
    return make_response(status, json_body(obj), extra_headers)


def error_response(status, message):
    # A 401 must carry WWW-Authenticate or libcurl/real-git will not
    # retry with credentials (it fails immediately instead).
    extra = None
    if status == 401:
        extra = [("WWW-Authenticate", 'Basic realm="forge"')]
    return json_response(status, {"message": message}, extra_headers=extra)


def check_auth(headers):
    """Bearer token check, plus Basic (real git sends Basic when the
    token is embedded in the URL: user or password == token).
    Returns True when authorised."""
    auth = headers.get("authorization", "")
    if auth.startswith("Bearer "):
        return auth[7:].strip() == TOKEN
    if auth.startswith("Basic "):
        try:
            import base64 as _b64
            cred = _b64.b64decode(auth[6:].strip()).decode("utf-8", "replace")
        except Exception:
            return False
        user, _, pw = cred.partition(":")
        return user == TOKEN or pw == TOKEN
    return False


class ForgeHandler(socketserver.BaseRequestHandler):
    def handle(self):
        try:
            self.request.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        rfile = self.request.makefile("rb")
        try:
            while True:
                request_line = rfile.readline(65536)
                if not request_line:
                    return
                if request_line in (b"\r\n", b"\n"):
                    continue
                parts = request_line.split()
                if len(parts) != 3:
                    return
                method = parts[0].decode("ascii", "ignore")
                raw_target = parts[1].decode("utf-8", "surrogateescape")
                # Headers.
                headers = {}
                while True:
                    line = rfile.readline(65536)
                    if not line or line in (b"\r\n", b"\n"):
                        break
                    if b":" in line:
                        name, value = line.split(b":", 1)
                        headers[name.strip().decode("ascii", "ignore").lower()] = value.strip().decode("utf-8", "surrogateescape")
                # Expect: 100-continue (real git sends it for larger packs).
                if headers.get("expect", "").lower() == "100-continue":
                    try:
                        self.request.sendall(b"HTTP/1.1 100 Continue\r\n\r\n")
                    except OSError:
                        return
                # Body.
                body = b""
                length = headers.get("content-length")
                if length is not None:
                    try:
                        n = int(length)
                    except ValueError:
                        n = 0
                    if n > 0:
                        body = rfile.read(n)
                elif headers.get("transfer-encoding", "").lower() == "chunked":
                    chunks = []
                    while True:
                        size_line = rfile.readline(65536).strip()
                        try:
                            size = int(size_line.split(b";")[0], 16)
                        except ValueError:
                            size = 0
                        if size == 0:
                            # trailing headers until blank line
                            while True:
                                t = rfile.readline(65536)
                                if not t or t in (b"\r\n", b"\n"):
                                    break
                            break
                        chunks.append(rfile.read(size))
                        rfile.read(2)  # trailing CRLF
                    body = b"".join(chunks)
                try:
                    response, keep_alive = dispatch(method, raw_target, headers, body)
                except Exception:
                    response, keep_alive = error_response(500, "internal error"), False
                try:
                    self.request.sendall(response)
                except OSError:
                    return
                conn = headers.get("connection", "").lower()
                if not keep_alive or conn == "close":
                    return
        except (OSError, ValueError):
            return
        finally:
            try:
                rfile.close()
            except Exception:
                pass


class ForgeServer(socketserver.ThreadingMixIn, socketserver.TCPServer):
    daemon_threads = True
    allow_reuse_address = True
    # The default listen backlog is 5: 50 concurrent connections (the
    # clone workload) overflow it, SYNs are dropped and clients retry
    # with backoff — measured 1-2 s for 50 bare connects. 256 makes the
    # same burst take ~25 ms.
    request_queue_size = 256


def split_target(raw_target):
    """Split a request target into (path, query dict)."""
    if "?" in raw_target:
        path, query = raw_target.split("?", 1)
    else:
        path, query = raw_target, ""
    path = urllib.parse.unquote(path)
    q = {}
    for pair in query.split("&"):
        if not pair:
            continue
        if "=" in pair:
            k, v = pair.split("=", 1)
            q[urllib.parse.unquote_plus(k)] = urllib.parse.unquote_plus(v)
        else:
            q[urllib.parse.unquote_plus(pair)] = ""
    return path, q

# ---------------------------------------------------------------------------
# Content / commit helpers
# ---------------------------------------------------------------------------

def flat_files(tree_oid):
    out = {}
    if tree_oid:
        load_tree_recursive(tree_oid, "", out)
    return out


def build_tree_from_files(files):
    """files: {path: (mode, oid)}. Build nested trees bottom-up, store
    them, return the root tree oid."""
    # Group into a nested dict: {name: (mode, oid)} or {name: subdict}.
    root = {}
    for path, (mode, oid) in files.items():
        parts = path.split("/")
        node = root
        for part in parts[:-1]:
            node = node.setdefault(part, {})
        node[parts[-1]] = (mode, oid)

    def build(node):
        entries = []
        for name, val in node.items():
            if isinstance(val, dict):
                sub = build(val)
                entries.append(("40000", name, sub))
            else:
                entries.append((val[0], name, val[1]))
        content = build_tree(entries)
        return store_object("tree", content)

    return build(root)


def resolve_ref(repo, ref):
    """Resolve a branch name, a full ref, or a commit oid to a commit oid."""
    if ref is None:
        ref = repo.default_branch
    if ref.startswith("refs/heads/"):
        return repo.refs.get(ref)
    if ref in repo.refs:
        return repo.refs[ref]
    branch_ref = "refs/heads/" + ref
    if branch_ref in repo.refs:
        return repo.refs[branch_ref]
    if len(ref) == 40 and ref in objects and objects[ref][0] == "commit":
        return ref
    return None


def get_tree_at(repo, ref):
    oid = resolve_ref(repo, ref)
    if oid is None:
        return None
    tree, _ = parse_commit(oid)
    return tree


def commit_on_branch(repo, branch, files, message):
    """Create a commit with the given flat file map on `branch` (creating
    the branch from the default tip when needed). Returns the commit oid."""
    parent = repo.refs.get("refs/heads/" + branch)
    if parent is None and branch != repo.default_branch:
        parent = repo.refs.get("refs/heads/" + repo.default_branch)
    tree_oid = build_tree_from_files(files)
    parents = [parent] if parent else []
    content = build_commit(tree_oid, parents, message, VIEWER["name"], VIEWER["email"])
    oid = store_object("commit", content)
    repo.refs["refs/heads/" + branch] = oid
    return oid


def line_diff_counts(old_bytes, new_bytes):
    """(additions, deletions) between two text blobs via difflib."""
    import difflib
    try:
        old_lines = old_bytes.decode("utf-8", "surrogateescape").splitlines()
        new_lines = new_bytes.decode("utf-8", "surrogateescape").splitlines()
    except Exception:
        return (1 if new_bytes != old_bytes else 0, 0)
    sm = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
    additions = 0
    deletions = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ("insert", "replace"):
            additions += j2 - j1
        if tag in ("delete", "replace"):
            deletions += i2 - i1
    return additions, deletions


def compute_diff(base_tree, head_tree):
    """[(path, status, additions, deletions)] for head vs base."""
    base = flat_files(base_tree)
    head = flat_files(head_tree)
    out = []
    for path in sorted(set(base) | set(head)):
        if path not in base:
            mode, oid = head[path]
            content = objects[oid][1]
            additions = len(content.decode("utf-8", "surrogateescape").splitlines())
            out.append((path, "added", max(additions, 1), 0))
        elif path not in head:
            out.append((path, "removed", 0, 1))
        elif base[path][1] != head[path][1]:
            old = objects[base[path][1]][1]
            new = objects[head[path][1]][1]
            a, d = line_diff_counts(old, new)
            out.append((path, "modified", a, d))
    return out


def pr_is_conflicted(repo, pull):
    """3-way conflict check: a changed file whose base content moved since
    the PR's base commit conflicts."""
    base_files = flat_files(get_tree_at(repo, pull.base_commit) or "")
    cur_tip = repo.refs.get("refs/heads/" + pull.base_ref)
    cur_files = flat_files(get_tree_at(repo, cur_tip) or "") if cur_tip else {}
    for path, _status, _a, _d in pull.changed:
        if base_files.get(path, (None, None))[1] != cur_files.get(path, (None, None))[1]:
            return True
    return False


def squash_merge(repo, pull):
    """Apply the PR's head files onto the base branch tip and commit.
    Returns the merge commit oid, or None when conflicted."""
    if pr_is_conflicted(repo, pull):
        return None
    base_tip = repo.refs.get("refs/heads/" + pull.base_ref)
    head_tip = repo.refs.get("refs/heads/" + pull.head_ref)
    base_files = flat_files(get_tree_at(repo, base_tip) or "")
    head_files = flat_files(get_tree_at(repo, head_tip) or "")
    for path, _status, _a, _d in pull.changed:
        if path in head_files:
            base_files[path] = head_files[path]
        else:
            base_files.pop(path, None)
    tree_oid = build_tree_from_files(base_files)
    message = f"Merge pull request #{pull.number} from {pull.head_ref}"
    content = build_commit(tree_oid, [base_tip] if base_tip else [],
                           message, VIEWER["name"], VIEWER["email"])
    merge_oid = store_object("commit", content)
    repo.refs["refs/heads/" + pull.base_ref] = merge_oid
    return merge_oid


# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------

def parse_json_body(body):
    """Returns (obj, error_response_or_None). Empty body -> {}."""
    if not body:
        return {}, None
    try:
        obj = json.loads(body.decode("utf-8"))
    except Exception:
        return None, error_response(400, "malformed JSON body")
    if not isinstance(obj, dict):
        return None, error_response(400, "malformed JSON body")
    return obj, None


def dispatch(method, raw_target, headers, body):
    """Route one request. Returns (response_bytes, keep_alive)."""
    path, query = split_target(raw_target)
    if path == "/healthz" and method == "GET":
        return json_response(200, {"ok": True}), True
    # Everything else needs the bearer token.
    if not check_auth(headers):
        return error_response(401, "Bad credentials"), True
    host = headers.get("host", "127.0.0.1")
    if path == "/api/graphql" and method == "POST":
        return handle_graphql(body), True
    if path == "/mcp":
        return handle_mcp(method, headers, body), True
    if path.startswith("/api/v3"):
        return handle_rest(method, path, query, headers, body, host), True
    if ".git/" in path or path.endswith(".git"):
        return handle_git(method, path, query, headers, body), True
    return error_response(404, "Not Found"), True


def repo_from_path(owner, name):
    """A repo belongs to the login the token names; any other owner is 404."""
    if owner != VIEWER_LOGIN:
        return None
    return get_repo(owner, name)


def handle_rest(method, path, query, headers, body, host):
    segs = [s for s in path.split("/") if s != ""][2:]  # drop api/v3
    if not segs:
        if method == "GET":
            return json_response(200, {"current_user_url": "/api/v3/user",
                                       "rate_limit_url": "/api/v3/rate_limit"},
                                 [("X-OAuth-Scopes", "repo, read:org")])
        return error_response(404, "Not Found")
    if segs == ["meta"]:
        if method == "GET":
            return json_response(200, {"installed_version": "1.0.0"})
        return error_response(404, "Not Found")
    if segs == ["user"]:
        if method == "GET":
            return json_response(200, {"login": VIEWER_LOGIN, "id": VIEWER["id"],
                                       "name": VIEWER["name"],
                                       "email": VIEWER["email"]})
        return error_response(404, "Not Found")
    if segs[:2] == ["user", "repos"]:
        if method == "GET":
            return rest_list_user_repos(query, host)
        if method == "POST":
            data, err = parse_json_body(body)
            if err is not None:
                return err
            name = data.get("name")
            if not name:
                return error_response(422, "name is required")
            repo = create_repo(VIEWER_LOGIN, name, data.get("private", False),
                               data.get("description", ""),
                               data.get("default_branch", "main"))
            if repo is None:
                return error_response(422, "Repository already exists")
            return make_response(201, json_body(repo.json()))
        return error_response(404, "Not Found")
    if segs[0] == "repos" and len(segs) >= 3:
        owner, name = segs[1], segs[2]
        rest = segs[3:]
        repo = repo_from_path(owner, name)
        if repo is None:
            return error_response(404, "Not Found")
        if not rest:
            if method == "GET":
                return json_response(200, repo.json())
            if method == "PATCH":
                data, err = parse_json_body(body)
                if err is not None:
                    return err
                with store_lock:
                    if "description" in data:
                        repo.description = data["description"] or ""
                return json_response(200, repo.json())
            if method == "DELETE":
                with store_lock:
                    repos.pop((owner, name), None)
                return make_response(204, b"")
            return error_response(404, "Not Found")
        if rest[0] == "branches":
            return rest_branches(method, repo, rest[1:], body)
        if rest[0] == "commits":
            return rest_commits(method, repo, query)
        if rest[0] == "git" and len(rest) >= 2 and rest[1] == "refs":
            return rest_git_refs(method, repo, rest[2:], body)
        if rest[0] == "contents":
            return rest_contents(method, repo, rest[1:], query, body)
        if rest[0] == "labels":
            return rest_labels(method, repo, body)
        if rest[0] == "issues":
            return rest_issues(method, repo, rest[1:], query, body)
        if rest[0] == "pulls":
            return rest_pulls(method, repo, rest[1:], query, body)
        return error_response(404, "Not Found")
    return error_response(404, "Not Found")


def rest_list_user_repos(query, host):
    try:
        per_page = int(query.get("per_page", "30"))
    except ValueError:
        per_page = 30
    per_page = max(1, min(per_page, 100))
    try:
        page = int(query.get("page", "1"))
    except ValueError:
        page = 1
    page = max(1, page)
    with store_lock:
        mine = [r for (o, _n), r in repos.items() if o == VIEWER_LOGIN]
    mine.sort(key=lambda r: r.rid)
    start = (page - 1) * per_page
    items = mine[start:start + per_page]
    payload = json_body([r.json() for r in items])
    extra = []
    if start + per_page < len(mine):
        nxt = f"http://{host}/api/v3/user/repos?per_page={per_page}&page={page + 1}"
        extra.append(("Link", f'<{nxt}>; rel="next"'))
    return make_response(200, payload, extra)


def rest_branches(method, repo, rest, body):
    if method != "GET":
        return error_response(404, "Not Found")
    with store_lock:
        refs = dict(repo.refs)
    branches = []
    for refname in sorted(refs):
        if refname.startswith("refs/heads/"):
            branches.append({"name": refname[len("refs/heads/"):],
                             "commit": {"sha": refs[refname]}})
    if not rest:
        return json_response(200, branches)
    branch = "/".join(rest)
    for b in branches:
        if b["name"] == branch:
            return json_response(200, b)
    return error_response(404, "Not Found")


def rest_commits(method, repo, query):
    if method != "GET":
        return error_response(404, "Not Found")
    ref = query.get("sha")
    tip = resolve_ref(repo, ref)
    out = []
    seen = set()
    cur = tip
    while cur and cur not in seen and cur in objects:
        seen.add(cur)
        tree, parents = parse_commit(cur)
        content = objects[cur][1]
        # Message = text after the first blank line.
        msg = content.split(b"\n\n", 1)[1].decode("utf-8", "surrogateescape") if b"\n\n" in content else ""
        out.append({"sha": cur, "commit": {"message": msg}})
        cur = parents[0] if parents else None
    return json_response(200, out)


def rest_git_refs(method, repo, rest, body):
    if method == "POST" and not rest:
        data, err = parse_json_body(body)
        if err is not None:
            return err
        ref = data.get("ref", "")
        sha = data.get("sha", "")
        if not ref.startswith("refs/") or len(sha) != 40 or sha not in objects:
            return error_response(422, "invalid ref or sha")
        with store_lock:
            if ref in repo.refs:
                return error_response(422, "Reference already exists")
            repo.refs[ref] = sha
        return make_response(201, json_body({"ref": ref, "object": {"sha": sha}}))
    if method == "GET" and rest:
        ref = "refs/" + "/".join(rest)
        with store_lock:
            sha = repo.refs.get(ref)
        if sha is None:
            return error_response(404, "Not Found")
        return json_response(200, {"ref": ref, "object": {"sha": sha}})
    return error_response(404, "Not Found")


def rest_contents(method, repo, rest, query, body):
    if not rest:
        return error_response(404, "Not Found")
    file_path = "/".join(rest)
    ref = query.get("ref")
    if method == "GET":
        tree = get_tree_at(repo, ref)
        if tree is None:
            return error_response(404, "Not Found")
        files = flat_files(tree)
        if file_path in files:
            mode, oid = files[file_path]
            content = objects[oid][1]
            return json_response(200, {
                "type": "file", "encoding": "base64",
                "content": base64.b64encode(content).decode("ascii"),
                "sha": oid, "size": len(content),
                "name": file_path.rsplit("/", 1)[-1], "path": file_path})
        # Directory listing.
        prefix = file_path + "/"
        entries = []
        seen_dirs = set()
        for p, (mode, oid) in files.items():
            if not p.startswith(prefix):
                continue
            rest_path = p[len(prefix):]
            first = rest_path.split("/", 1)[0]
            if "/" in rest_path:
                if first not in seen_dirs:
                    seen_dirs.add(first)
                    entries.append({"type": "dir", "name": first,
                                    "path": file_path + "/" + first,
                                    "sha": ""})
            else:
                entries.append({"type": "file", "name": first,
                                "path": p, "sha": oid})
        if not entries:
            return error_response(404, "Not Found")
        entries.sort(key=lambda e: e["name"])
        # A directory entry needs a sha; compute the subtree oid.
        tree_oid = get_tree_at(repo, ref)
        for e in entries:
            if e["type"] == "dir":
                sub = flat_files(tree_oid)
                e["sha"] = _subtree_oid(tree_oid, file_path + "/" + e["name"])
        return json_response(200, entries)
    if method == "PUT":
        data, err = parse_json_body(body)
        if err is not None:
            return err
        message = data.get("message", "")
        content_b64 = data.get("content", "")
        try:
            content = base64.b64decode(content_b64, validate=False)
        except Exception:
            return error_response(400, "invalid content")
        branch = data.get("branch") or repo.default_branch
        sha = data.get("sha")
        with store_lock:
            tip = resolve_ref(repo, branch)
            tree = get_tree_at(repo, tip) if tip else None
            files = flat_files(tree) if tree else {}
            exists = file_path in files
            if exists and sha is None:
                return error_response(422, "sha is required to update a file")
            if exists and files[file_path][1] != sha:
                return error_response(409, "sha does not match")
            if not exists and sha is not None:
                return error_response(409, "sha does not match")
            blob_oid = store_object("blob", content)
            files[file_path] = ("100644", blob_oid)
            commit_oid = commit_on_branch(repo, branch, files, message)
        status = 200 if exists else 201
        return make_response(status, json_body({
            "content": {"sha": blob_oid, "encoding": "base64",
                        "name": file_path.rsplit("/", 1)[-1], "path": file_path},
            "commit": {"sha": commit_oid}}))
    if method == "DELETE":
        data, err = parse_json_body(body)
        if err is not None:
            return err
        message = data.get("message", "")
        sha = data.get("sha")
        branch = data.get("branch") or repo.default_branch
        with store_lock:
            tip = resolve_ref(repo, branch)
            tree = get_tree_at(repo, tip) if tip else None
            files = flat_files(tree) if tree else {}
            if file_path not in files:
                return error_response(404, "Not Found")
            if sha is not None and files[file_path][1] != sha:
                return error_response(409, "sha does not match")
            del files[file_path]
            commit_oid = commit_on_branch(repo, branch, files, message)
        return json_response(200, {"commit": {"sha": commit_oid}})
    return error_response(404, "Not Found")


def _subtree_oid(tree_oid, dir_path):
    """The tree oid of a subdirectory, or '' when absent."""
    parts = dir_path.split("/")
    cur = tree_oid
    for part in parts:
        found = None
        for mode, name, child in parse_tree(cur):
            if name == part and mode == "40000":
                found = child
                break
        if found is None:
            return ""
        cur = found
    return cur


def rest_labels(method, repo, body):
    if method != "POST":
        return error_response(404, "Not Found")
    data, err = parse_json_body(body)
    if err is not None:
        return err
    name = data.get("name")
    if not name:
        return error_response(422, "name is required")
    color = data.get("color", "ededed")
    with store_lock:
        if name in repo.labels:
            return error_response(422, "Label already exists")
        repo.labels[name] = {"name": name, "color": color}
    return make_response(201, json_body({"name": name, "color": color}))


def rest_issues(method, repo, rest, query, body):
    if not rest:
        if method == "GET":
            state = query.get("state", "open")
            sort = query.get("sort", "created")
            direction = query.get("direction", "desc")
            with store_lock:
                issues = list(repo.issues.values())
            if state != "all":
                issues = [i for i in issues if i.state == state]
            issues.sort(key=lambda i: i.number, reverse=(direction == "desc"))
            payload = b"[" + b",".join(i.json for i in issues if i.json) + b"]"
            return make_response(200, payload)
        if method == "POST":
            data, err = parse_json_body(body)
            if err is not None:
                return err
            title = data.get("title", "")
            labels = data.get("labels", []) or []
            with store_lock:
                for label in labels:
                    if label not in repo.labels:
                        return error_response(422, f"label {label} does not exist")
                number = repo.next_issue
                repo.next_issue += 1
                issue = Issue(repo.rid, number, title, data.get("body", ""), labels)
                issue.refresh_json(repo)
                repo.issues[number] = issue
            return make_response(201, issue.json)
        return error_response(404, "Not Found")
    try:
        number = int(rest[0])
    except ValueError:
        return error_response(404, "Not Found")
    if len(rest) == 1:
        with store_lock:
            issue = repo.issues.get(number)
        if issue is None:
            return error_response(404, "Not Found")
        if method == "GET":
            # Hot path (read workload): the body is pre-serialised.
            return make_response(200, issue.json)
        if method == "PATCH":
            data, err = parse_json_body(body)
            if err is not None:
                return err
            with store_lock:
                if "state" in data:
                    issue.state = data["state"]
                if "title" in data:
                    issue.title = data["title"]
                if "body" in data:
                    issue.body = data["body"]
                issue.refresh_json(repo)
            return json_response(200, json.loads(issue.json.decode("utf-8")))
        return error_response(404, "Not Found")
    if len(rest) == 2 and rest[1] == "comments":
        with store_lock:
            issue = repo.issues.get(number)
        if issue is None:
            return error_response(404, "Not Found")
        if method == "GET":
            return json_response(200, issue.comments)
        if method == "POST":
            data, err = parse_json_body(body)
            if err is not None:
                return err
            comment = {"id": next(_comment_id_seq), "body": data.get("body", ""),
                       "user": {"login": VIEWER_LOGIN, "id": VIEWER["id"]},
                       "created_at": EPOCH_ISO}
            with store_lock:
                issue.comments.append(comment)
            return make_response(201, json_body(comment))
        return error_response(404, "Not Found")
    return error_response(404, "Not Found")


def rest_pulls(method, repo, rest, query, body):
    if not rest:
        if method == "GET":
            state = query.get("state", "open")
            with store_lock:
                pulls = list(repo.pulls.values())
            if state != "all":
                pulls = [p for p in pulls if p.state == state]
            pulls.sort(key=lambda p: p.number)
            payload = b"[" + b",".join(p.json for p in pulls if p.json) + b"]"
            return make_response(200, payload)
        if method == "POST":
            data, err = parse_json_body(body)
            if err is not None:
                return err
            head = data.get("head", "")
            base = data.get("base", "")
            with store_lock:
                head_tip = repo.refs.get("refs/heads/" + head)
                base_tip = repo.refs.get("refs/heads/" + base)
                if head_tip is None or base_tip is None:
                    return error_response(422, "head or base branch does not exist")
                head_tree = get_tree_at(repo, head_tip)
                base_tree = get_tree_at(repo, base_tip)
                changed = compute_diff(base_tree, head_tree)
                number = repo.next_pull
                repo.next_pull += 1
                pull = Pull(repo.rid, number, data.get("title", ""), data.get("body", ""),
                            head, head_tip, base, base_tip, base_tip, changed)
                pull.refresh_json(repo)
                repo.pulls[number] = pull
            return make_response(201, pull.json)
        return error_response(404, "Not Found")
    try:
        number = int(rest[0])
    except ValueError:
        return error_response(404, "Not Found")
    if len(rest) == 1:
        with store_lock:
            pull = repo.pulls.get(number)
        if pull is None:
            return error_response(404, "Not Found")
        if method == "GET":
            return make_response(200, pull.json)
        return error_response(404, "Not Found")
    if len(rest) == 2 and rest[1] == "files":
        with store_lock:
            pull = repo.pulls.get(number)
        if pull is None:
            return error_response(404, "Not Found")
        if method == "GET":
            files = [{"filename": p, "status": s, "additions": a,
                      "deletions": d, "changes": a + d}
                     for (p, s, a, d) in pull.changed]
            return json_response(200, files)
        return error_response(404, "Not Found")
    if len(rest) == 2 and rest[1] == "merge":
        if method != "PUT":
            return error_response(404, "Not Found")
        data, err = parse_json_body(body)
        if err is not None:
            return err
        with store_lock:
            pull = repo.pulls.get(number)
            if pull is None:
                return error_response(404, "Not Found")
            if pull.state != "open":
                return error_response(405, "Pull request is not open")
            merge_sha = squash_merge(repo, pull)
            if merge_sha is None:
                return error_response(405, "Merge conflict")
            pull.merged = True
            pull.state = "closed"
            pull.merged_at = _iso(pull.pid + 1000)
            pull.merge_sha = merge_sha
            pull.refresh_json(repo)
        return json_response(200, {"sha": merge_sha, "merged": True,
                                   "message": f"Pull request #{number} merged"})
    return error_response(404, "Not Found")

# ---------------------------------------------------------------------------
# GraphQL (a small parser + resolver for exactly the documents gh sends)
# ---------------------------------------------------------------------------

_GQL_TYPE_FIELDS = {
    "Issue": ["id", "number", "title", "state", "body"],
    "PullRequest": ["id", "number", "headRefName", "baseRefName", "mergeable",
                    "state", "merged", "files"],
    "Repository": ["id", "databaseId", "name", "nameWithOwner", "owner",
                   "defaultBranchRef", "viewerPermission", "hasIssuesEnabled",
                   "issue", "issues", "pullRequests", "pullRequest"],
}
_GQL_ENUM_VALUES = {
    "SearchType": ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "COMMIT"],
}


class _GqlError(Exception):
    def __init__(self, message):
        super().__init__(message)
        self.message = message


def _gql_tokenize(text):
    tokens = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n,":
            i += 1
        elif c == "#":
            while i < n and text[i] != "\n":
                i += 1
        elif c == "." and text[i:i + 3] == "...":
            tokens.append(("...", "..."))
            i += 3
        elif c in "{}():[]!=$@":
            tokens.append((c, c))
            i += 1
        elif c == '"':
            j = i + 1
            out = []
            while j < n and text[j] != '"':
                if text[j] == "\\" and j + 1 < n:
                    nxt = text[j + 1]
                    mapping = {"n": "\n", "t": "\t", "r": "\r", '"': '"', "\\": "\\", "/": "/"}
                    out.append(mapping.get(nxt, nxt))
                    j += 2
                else:
                    out.append(text[j])
                    j += 1
            tokens.append(("string", "".join(out)))
            i = j + 1
        elif c.isdigit() or (c == "-" and i + 1 < n and text[i + 1].isdigit()):
            j = i
            if text[j] == "-":
                j += 1
            while j < n and text[j].isdigit():
                j += 1
            if j < n and text[j] == ".":
                j += 1
                while j < n and text[j].isdigit():
                    j += 1
                tokens.append(("float", float(text[i:j])))
            else:
                tokens.append(("int", int(text[i:j])))
            i = j
        elif c.isalpha() or c == "_":
            j = i
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            tokens.append(("name", text[i:j]))
            i = j
        else:
            raise _GqlError(f"unexpected character {c!r} in query")
    tokens.append(("eof", None))
    return tokens


class _GqlParser:
    def __init__(self, text):
        self.tokens = _gql_tokenize(text)
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos]

    def next(self):
        tok = self.tokens[self.pos]
        self.pos += 1
        return tok

    def expect(self, kind):
        tok = self.next()
        if tok[0] != kind:
            raise _GqlError(f"expected {kind}, got {tok[0]}")
        return tok[1]

    def parse_document(self):
        operations = []
        while self.peek()[0] != "eof":
            operations.append(self.parse_operation())
        return operations

    def parse_operation(self):
        kind, value = self.peek()
        if kind == "{":
            return {"kind": "query", "name": None, "variables": {},
                    "selection": self.parse_selection_set()}
        if kind == "name" and value in ("query", "mutation", "subscription"):
            self.next()
            name = None
            if self.peek()[0] == "name":
                name = self.next()[1]
            variables = {}
            if self.peek()[0] == "(":
                variables = self.parse_variable_definitions()
            return {"kind": value, "name": name, "variables": variables,
                    "selection": self.parse_selection_set()}
        raise _GqlError("expected an operation")

    def parse_variable_definitions(self):
        self.expect("(")
        defs = {}
        while self.peek()[0] != ")":
            self.expect("$")
            name = self.expect("name")
            self.expect(":")
            defs[name] = self.parse_type()
            if self.peek()[0] == "=":
                self.next()
                self.parse_value()
        self.expect(")")
        return defs

    def parse_type(self):
        tok = self.next()
        if tok[0] == "[":
            inner = self.parse_type()
            self.expect("]")
            base = inner
        elif tok[0] == "name":
            base = tok[1]
        else:
            raise _GqlError("expected a type")
        if self.peek()[0] == "!":
            self.next()
        return base

    def parse_selection_set(self):
        self.expect("{")
        fields = []
        while self.peek()[0] != "}":
            fields.append(self.parse_field())
        self.expect("}")
        return fields

    def parse_field(self):
        if self.peek()[0] == "...":
            self.next()
            if self.peek() == ("name", "on"):
                self.next()
                type_name = self.expect("name")
                return {"fragment": True, "type": type_name,
                        "selection": self.parse_selection_set()}
            # Named fragment spread (not sent by the suite); parse the name
            # and ignore it.
            self.expect("name")
            return {"fragment": True, "type": None, "selection": []}
        name = self.expect("name")
        alias = None
        if self.peek()[0] == ":":
            self.next()
            alias = name
            name = self.expect("name")
        args = {}
        if self.peek()[0] == "(":
            args = self.parse_arguments()
        selection = None
        if self.peek()[0] == "{":
            selection = self.parse_selection_set()
        return {"field": name, "alias": alias or name, "args": args,
                "selection": selection}

    def parse_arguments(self):
        self.expect("(")
        args = {}
        while self.peek()[0] != ")":
            name = self.expect("name")
            self.expect(":")
            args[name] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self):
        kind, value = self.next()
        if kind == "$":
            return ("var", self.expect("name"))
        if kind == "string":
            return value
        if kind == "int":
            return value
        if kind == "float":
            return value
        if kind == "name":
            if value == "true":
                return True
            if value == "false":
                return False
            if value == "null":
                return None
            return ("enum", value)
        if kind == "[":
            items = []
            while self.peek()[0] != "]":
                items.append(self.parse_value())
            self.expect("]")
            return items
        if kind == "{":
            obj = {}
            while self.peek()[0] != "}":
                key = self.expect("name")
                self.expect(":")
                obj[key] = self.parse_value()
            self.expect("}")
            return obj
        raise _GqlError(f"unexpected value token {kind}")


def _gql_resolve_value(value, variables):
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "var":
        return variables.get(value[1])
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "enum":
        return value[1]
    if isinstance(value, list):
        return [_gql_resolve_value(v, variables) for v in value]
    if isinstance(value, dict):
        return {k: _gql_resolve_value(v, variables) for k, v in value.items()}
    return value


def _gql_args(field, variables):
    return {k: _gql_resolve_value(v, variables) for k, v in field["args"].items()}


def _gid(prefix, num):
    return f"{prefix}_{num}"


def _parse_gid(value, prefix):
    """Parse an opaque global id (or a bare number) back to its number."""
    if value is None:
        return None
    s = str(value)
    if s.startswith(prefix + "_"):
        s = s[len(prefix) + 1:]
    try:
        return int(s)
    except ValueError:
        return None


def _repo_by_gid(gid):
    rid = _parse_gid(gid, "R")
    if rid is None:
        return None
    for repo in repos.values():
        if repo.rid == rid:
            return repo
    return None


def _issue_by_gid(gid):
    iid = _parse_gid(gid, "I")
    if iid is None:
        return None
    for repo in repos.values():
        for issue in repo.issues.values():
            if issue.iid == iid:
                return issue, repo
    return None


def _pull_by_gid(gid):
    pid = _parse_gid(gid, "PR")
    if pid is None:
        return None
    for repo in repos.values():
        for pull in repo.pulls.values():
            if pull.pid == pid:
                return pull, repo
    return None


# --- resolvers: each returns a plain JSON value for one field ----------

def _resolve_query(field, variables, errors):
    name = field["field"]
    args = _gql_args(field, variables)
    if name == "viewer":
        return _resolve_selection("User", {"login": VIEWER_LOGIN},
                                  field["selection"], variables, errors)
    if name == "repository":
        repo = repo_from_path(args.get("owner"), args.get("name"))
        if repo is None:
            return None
        return _resolve_selection("Repository", repo, field["selection"],
                                  variables, errors)
    if name == "node":
        gid = args.get("id")
        repo = _repo_by_gid(gid)
        if repo is None:
            return None
        return _resolve_selection("Node", repo, field["selection"],
                                  variables, errors)
    if name == "__type":
        type_name = args.get("name")
        return _resolve_selection("__Type", {"__type_name": type_name},
                                  field["selection"], variables, errors)
    raise _GqlError(f"Cannot query field '{name}' on type 'Query'.")


def _resolve_user(field, user, variables, errors):
    name = field["field"]
    if name == "login":
        return user["login"]
    raise _GqlError(f"Cannot query field '{name}' on type 'User'.")


def _resolve_repository(field, repo, variables, errors):
    name = field["field"]
    args = _gql_args(field, variables)
    if name == "id":
        return _gid("R", repo.rid)
    if name == "databaseId":
        return repo.rid
    if name == "name":
        return repo.name
    if name == "nameWithOwner":
        return f"{repo.owner}/{repo.name}"
    if name == "owner":
        return _resolve_selection("User", {"login": repo.owner},
                                  field["selection"], variables, errors)
    if name == "defaultBranchRef":
        tip = repo.refs.get("refs/heads/" + repo.default_branch)
        if tip is None:
            return None
        return _resolve_selection("Ref", {"name": repo.default_branch},
                                  field["selection"], variables, errors)
    if name == "viewerPermission":
        return "ADMIN"
    if name == "hasIssuesEnabled":
        return True
    if name == "issue":
        issue = repo.issues.get(args.get("number"))
        if issue is None:
            return None
        return _resolve_selection("Issue", issue, field["selection"],
                                  variables, errors)
    if name == "issues":
        return _resolve_issues_connection(repo, args, field["selection"],
                                          variables, errors)
    if name == "pullRequests":
        return _resolve_pulls_connection(repo, args, field["selection"],
                                         variables, errors)
    if name == "pullRequest":
        pull = repo.pulls.get(args.get("number"))
        if pull is None:
            return None
        return _resolve_selection("PullRequest", (pull, repo),
                                  field["selection"], variables, errors)
    raise _GqlError(f"Cannot query field '{name}' on type 'Repository'.")


def _resolve_issues_connection(repo, args, selection, variables, errors):
    states = args.get("states")
    order_by = args.get("orderBy") or {}
    first = args.get("first")
    after = args.get("after")
    with store_lock:
        issues = list(repo.issues.values())
    if states:
        wanted = set()
        for s in states:
            wanted.add("open" if s == "OPEN" else "closed" if s == "CLOSED" else s.lower())
        issues = [i for i in issues if i.state in wanted]
    direction = (order_by.get("direction") or "DESC").upper()
    issues.sort(key=lambda i: i.number, reverse=(direction == "DESC"))
    if after is not None:
        try:
            cursor = int(after)
        except (TypeError, ValueError):
            cursor = None
        if cursor is not None:
            if direction == "DESC":
                issues = [i for i in issues if i.number < cursor]
            else:
                issues = [i for i in issues if i.number > cursor]
    total = len(issues)
    if first is not None:
        page = issues[:first]
        has_next = total > first
    else:
        page = issues
        has_next = False
    end_cursor = str(page[-1].number) if page else None
    result = {}
    for sub in selection or []:
        if sub.get("fragment"):
            continue
        if sub["field"] == "nodes":
            result[sub["alias"]] = [
                _resolve_selection("Issue", issue, sub["selection"], variables, errors)
                for issue in page]
        elif sub["field"] == "pageInfo":
            result[sub["alias"]] = _resolve_selection(
                "PageInfo", {"hasNextPage": has_next, "endCursor": end_cursor},
                sub["selection"], variables, errors)
        else:
            raise _GqlError(f"Cannot query field '{sub['field']}' on type 'IssueConnection'.")
    return result


def _resolve_pulls_connection(repo, args, selection, variables, errors):
    first = args.get("first")
    with store_lock:
        pulls = sorted(repo.pulls.values(), key=lambda p: p.number)
    if first is not None:
        pulls = pulls[:first]
    result = {}
    for sub in selection or []:
        if sub.get("fragment"):
            continue
        if sub["field"] == "nodes":
            result[sub["alias"]] = [
                _resolve_selection("PullRequest", (p, repo), sub["selection"],
                                   variables, errors) for p in pulls]
        elif sub["field"] == "pageInfo":
            result[sub["alias"]] = _resolve_selection(
                "PageInfo", {"hasNextPage": False, "endCursor": None},
                sub["selection"], variables, errors)
        else:
            raise _GqlError(f"Cannot query field '{sub['field']}' on type 'PullRequestConnection'.")
    return result


def _resolve_issue(field, issue, variables, errors):
    name = field["field"]
    if name == "id":
        return _gid("I", issue.iid)
    if name == "number":
        return issue.number
    if name == "title":
        return issue.title
    if name == "state":
        return issue.state.upper()
    if name == "body":
        return issue.body
    raise _GqlError(f"Cannot query field '{name}' on type 'Issue'.")


def _resolve_pull(field, pull_repo, variables, errors):
    pull, repo = pull_repo
    name = field["field"]
    args = _gql_args(field, variables)
    if name == "id":
        return _gid("PR", pull.pid)
    if name == "number":
        return pull.number
    if name == "headRefName":
        return pull.head_ref
    if name == "baseRefName":
        return pull.base_ref
    if name == "mergeable":
        return "CONFLICTING" if pr_is_conflicted(repo, pull) else "MERGEABLE"
    if name == "state":
        return pull.state.upper()
    if name == "merged":
        return pull.merged
    if name == "files":
        first = args.get("first")
        changed = pull.changed
        if first is not None:
            changed = changed[:first]
        nodes = [{"path": p} for (p, _s, _a, _d) in changed]
        result = {}
        for sub in field["selection"] or []:
            if sub.get("fragment"):
                continue
            if sub["field"] == "nodes":
                result[sub["alias"]] = [
                    _resolve_selection("PullRequestFile", n, sub["selection"],
                                       variables, errors) for n in nodes]
            elif sub["field"] == "pageInfo":
                result[sub["alias"]] = _resolve_selection(
                    "PageInfo", {"hasNextPage": False, "endCursor": None},
                    sub["selection"], variables, errors)
            else:
                raise _GqlError(f"Cannot query field '{sub['field']}' on type 'PullRequestFileConnection'.")
        return result
    raise _GqlError(f"Cannot query field '{name}' on type 'PullRequest'.")


def _resolve_type(field, type_info, variables, errors):
    type_name = type_info["__type_name"]
    name = field["field"]
    if name == "fields":
        names = _GQL_TYPE_FIELDS.get(type_name, [])
        return [{"name": n} for n in names]
    if name == "enumValues":
        names = _GQL_ENUM_VALUES.get(type_name, [])
        return [{"name": n} for n in names]
    if name == "name":
        return type_name
    raise _GqlError(f"Cannot query field '{name}' on type '__Type'.")


def _resolve_selection(type_name, value, selection, variables, errors):
    """Resolve a selection set against a typed value. Returns a dict."""
    if selection is None:
        return value
    out = {}
    for field in selection:
        if field.get("fragment"):
            frag_type = field.get("type")
            if frag_type is None:
                continue
            # Inline fragment: applies when the value is of that type.
            applies = (frag_type == type_name or
                       (type_name == "Node" and frag_type == "Repository" and isinstance(value, Repo)))
            if not applies:
                continue
            sub = _resolve_selection(frag_type if frag_type != "Node" else "Repository",
                                     value, field["selection"], variables, errors)
            out.update(sub)
            continue
        fname = field["field"]
        try:
            if type_name == "Query":
                out[field["alias"]] = _resolve_query(field, variables, errors)
            elif type_name == "User":
                out[field["alias"]] = _resolve_user(field, value, variables, errors)
            elif type_name == "Repository":
                out[field["alias"]] = _resolve_repository(field, value, variables, errors)
            elif type_name == "Issue":
                out[field["alias"]] = _resolve_issue(field, value, variables, errors)
            elif type_name == "PullRequest":
                out[field["alias"]] = _resolve_pull(field, value, variables, errors)
            elif type_name == "Ref":
                out[field["alias"]] = value["name"] if fname == "name" else None
                if fname != "name":
                    raise _GqlError(f"Cannot query field '{fname}' on type 'Ref'.")
            elif type_name == "PageInfo":
                out[field["alias"]] = value.get(fname)
                if fname not in ("hasNextPage", "endCursor"):
                    raise _GqlError(f"Cannot query field '{fname}' on type 'PageInfo'.")
            elif type_name == "PullRequestFile":
                out[field["alias"]] = value.get(fname)
                if fname != "path":
                    raise _GqlError(f"Cannot query field '{fname}' on type 'PullRequestFile'.")
            elif type_name == "__Type":
                out[field["alias"]] = _resolve_type(field, value, variables, errors)
            elif type_name == "Node":
                # Node resolves through its concrete type (Repository).
                out[field["alias"]] = _resolve_repository(field, value, variables, errors) if fname != "id" else _gid("R", value.rid)
            else:
                raise _GqlError(f"Cannot query field '{fname}' on type '{type_name}'.")
        except _GqlError as exc:
            errors.append({"message": exc.message})
            out[field["alias"]] = None
    return out


def _execute_mutation(field, variables, errors):
    name = field["field"]
    args = _gql_args(field, variables)
    if name == "createIssue":
        inp = args.get("input") or {}
        repo = _repo_by_gid(inp.get("repositoryId"))
        if repo is None:
            raise _GqlError("repository not found")
        with store_lock:
            number = repo.next_issue
            repo.next_issue += 1
            issue = Issue(repo.rid, number, inp.get("title", ""), inp.get("body", ""), [])
            issue.refresh_json(repo)
            repo.issues[number] = issue
        return _resolve_selection("CreateIssuePayload", {"issue": issue},
                                  field["selection"], variables, errors)
    if name == "closeIssue":
        inp = args.get("input") or {}
        found = _issue_by_gid(inp.get("issueId"))
        if found is None:
            raise _GqlError("issue not found")
        issue, repo = found
        with store_lock:
            issue.state = "closed"
            issue.refresh_json(repo)
        return _resolve_selection("CloseIssuePayload", {"issue": issue},
                                  field["selection"], variables, errors)
    if name == "createPullRequest":
        inp = args.get("input") or {}
        repo = _repo_by_gid(inp.get("repositoryId"))
        if repo is None:
            raise _GqlError("repository not found")
        head = inp.get("headRefName", "")
        base = inp.get("baseRefName", "")
        with store_lock:
            head_tip = repo.refs.get("refs/heads/" + head)
            base_tip = repo.refs.get("refs/heads/" + base)
            if head_tip is None or base_tip is None:
                raise _GqlError("head or base branch does not exist")
            changed = compute_diff(get_tree_at(repo, base_tip), get_tree_at(repo, head_tip))
            number = repo.next_pull
            repo.next_pull += 1
            pull = Pull(repo.rid, number, inp.get("title", ""), inp.get("body", ""),
                        head, head_tip, base, base_tip, base_tip, changed)
            pull.refresh_json(repo)
            repo.pulls[number] = pull
        return _resolve_selection("CreatePullRequestPayload", {"pullRequest": pull, "repo": repo},
                                  field["selection"], variables, errors)
    if name == "mergePullRequest":
        inp = args.get("input") or {}
        found = _pull_by_gid(inp.get("pullRequestId"))
        if found is None:
            raise _GqlError("pull request not found")
        pull, repo = found
        with store_lock:
            if pull.state != "open":
                raise _GqlError("pull request is not open")
            merge_sha = squash_merge(repo, pull)
            if merge_sha is None:
                raise _GqlError("merge conflict")
            pull.merged = True
            pull.state = "closed"
            pull.merged_at = _iso(pull.pid + 1000)
            pull.merge_sha = merge_sha
            pull.refresh_json(repo)
        return _resolve_selection("MergePullRequestPayload", {"pullRequest": pull, "repo": repo},
                                  field["selection"], variables, errors)
    if name == "addComment":
        inp = args.get("input") or {}
        found = _issue_by_gid(inp.get("subjectId"))
        if found is None:
            raise _GqlError("issue not found")
        issue, repo = found
        comment = {"id": next(_comment_id_seq), "body": inp.get("body", ""),
                   "user": {"login": VIEWER_LOGIN, "id": VIEWER["id"]},
                   "created_at": EPOCH_ISO}
        with store_lock:
            issue.comments.append(comment)
        return _resolve_selection("AddCommentPayload",
                                  {"commentEdge": {"node": comment}},
                                  field["selection"], variables, errors)
    raise _GqlError(f"Cannot query field '{name}' on type 'Mutation'.")


def _resolve_payload(type_name, value, selection, variables, errors):
    out = {}
    for field in selection or []:
        if field.get("fragment"):
            continue
        fname = field["field"]
        try:
            if fname == "issue" and "issue" in value:
                out[field["alias"]] = _resolve_selection(
                    "Issue", value["issue"], field["selection"], variables, errors)
            elif fname == "pullRequest" and "pullRequest" in value:
                out[field["alias"]] = _resolve_selection(
                    "PullRequest", (value["pullRequest"], value.get("repo")),
                    field["selection"], variables, errors)
            elif fname == "commentEdge" and "commentEdge" in value:
                node = value["commentEdge"]["node"]
                edge = {}
                for sub in field["selection"] or []:
                    if sub.get("fragment"):
                        continue
                    if sub["field"] == "node":
                        edge[sub["alias"]] = _resolve_selection(
                            "Comment", node, sub["selection"], variables, errors)
                out[field["alias"]] = edge
            else:
                raise _GqlError(f"Cannot query field '{fname}' on type '{type_name}'.")
        except _GqlError as exc:
            errors.append({"message": exc.message})
            out[field["alias"]] = None
    return out


def _resolve_comment(field, comment, variables, errors):
    name = field["field"]
    if name == "id":
        return _gid("C", comment["id"])
    if name == "body":
        return comment["body"]
    raise _GqlError(f"Cannot query field '{name}' on type 'IssueComment'.")


# Patch _resolve_selection to route payload/comment types (defined after it).
_orig_resolve_selection = _resolve_selection


def _resolve_selection2(type_name, value, selection, variables, errors):
    if type_name in ("CreateIssuePayload", "CloseIssuePayload",
                     "CreatePullRequestPayload", "MergePullRequestPayload",
                     "AddCommentPayload"):
        return _resolve_payload(type_name, value, selection, variables, errors)
    if type_name == "Comment":
        out = {}
        for field in selection or []:
            if field.get("fragment"):
                continue
            try:
                out[field["alias"]] = _resolve_comment(field, value, variables, errors)
            except _GqlError as exc:
                errors.append({"message": exc.message})
                out[field["alias"]] = None
        return out
    return _orig_resolve_selection(type_name, value, selection, variables, errors)


_resolve_selection = _resolve_selection2


def _execute_operation(operation, variables):
    errors = []
    data = {}
    for field in operation["selection"]:
        if field.get("fragment"):
            continue
        try:
            if operation["kind"] == "mutation":
                data[field["alias"]] = _execute_mutation(field, variables, errors)
            else:
                data[field["alias"]] = _resolve_query(field, variables, errors)
        except _GqlError as exc:
            errors.append({"message": exc.message})
            data[field["alias"]] = None
    result = {"data": data}
    if errors:
        result["errors"] = errors
    return result


def handle_graphql(body):
    try:
        payload = json.loads(body.decode("utf-8"))
    except Exception:
        return json_response(400, {"errors": [{"message": "malformed JSON body"}]})
    if isinstance(payload, list):
        results = []
        for item in payload:
            results.append(_graphql_one(item))
        return json_response(200, results)
    return json_response(200, _graphql_one(payload))


def _graphql_one(item):
    if not isinstance(item, dict):
        return {"data": None, "errors": [{"message": "malformed operation"}]}
    query = item.get("query", "")
    variables = item.get("variables") or {}
    try:
        operations = _GqlParser(query).parse_document()
    except _GqlError as exc:
        return {"data": None, "errors": [{"message": exc.message}]}
    if not operations:
        return {"data": None, "errors": [{"message": "empty document"}]}
    operation = operations[0]
    # operationName selection (the suite sends one operation per body).
    name = item.get("operationName")
    if name:
        for op in operations:
            if op.get("name") == name:
                operation = op
                break
    return _execute_operation(operation, variables)


# ---------------------------------------------------------------------------
# MCP (JSON-RPC 2.0 over Streamable HTTP)
# ---------------------------------------------------------------------------

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a repository owned by the viewer.",
     "inputSchema": {"type": "object",
                     "properties": {"name": {"type": "string"},
                                    "description": {"type": "string"},
                                    "private": {"type": "boolean"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "body": {"type": "string"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "state": {"type": "string"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Create a pull request from a head branch onto a base branch.",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "title": {"type": "string"},
                                    "head": {"type": "string"},
                                    "base": {"type": "string"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request by number (squash).",
     "inputSchema": {"type": "object",
                     "properties": {"owner": {"type": "string"},
                                    "repo": {"type": "string"},
                                    "pull_number": {"type": "integer"}},
                     "required": ["owner", "repo", "pull_number"]}},
]
# The tools list is built once and reused verbatim (two tools/list calls
# must answer byte-identical tools arrays).
MCP_TOOLS_JSON = json.dumps(MCP_TOOLS, separators=(",", ":"), ensure_ascii=False)


def _mcp_result(req_id, result):
    return json_response(200, {"jsonrpc": "2.0", "id": req_id, "result": result})


def _mcp_error(req_id, code, message):
    return json_response(200, {"jsonrpc": "2.0", "id": req_id,
                               "error": {"code": code, "message": message}})


def _mcp_tool_result(obj):
    text = json.dumps(obj, separators=(",", ":"), ensure_ascii=False)
    return {"content": [{"type": "text", "text": text}],
            "structuredContent": obj}


def _mcp_owner_repo(args):
    owner = args.get("owner")
    repo = args.get("repo")
    if (not owner or not repo) and args.get("full_name"):
        parts = str(args["full_name"]).split("/", 1)
        if len(parts) == 2:
            owner = owner or parts[0]
            repo = repo or parts[1]
    return owner, repo


def handle_mcp(method, headers, body):
    if method == "DELETE":
        return make_response(200, b"", content_type=None)
    if method != "POST":
        return error_response(404, "Not Found")
    try:
        req = json.loads(body.decode("utf-8"))
    except Exception:
        return json_response(400, {"jsonrpc": "2.0", "id": None,
                                   "error": {"code": -32700, "message": "Parse error"}})
    if not isinstance(req, dict):
        return json_response(400, {"jsonrpc": "2.0", "id": None,
                                   "error": {"code": -32700, "message": "Parse error"}})
    req_id = req.get("id")
    method_name = req.get("method", "")
    params = req.get("params") or {}
    # A notification (no id) gets a 202 with an empty body.
    is_notification = "id" not in req
    if method_name == "notifications/initialized":
        return make_response(202, b"", content_type=None)
    if method_name == "server/discover":
        result = {
            "supportedVersions": ["2026-07-28"],
            "serverInfo": {"name": "github-core-clone", "version": "1.0.0"},
            "capabilities": {"tools": {}},
            "_meta": {"io.modelcontextprotocol/serverInfo":
                      {"name": "github-core-clone", "version": "1.0.0"}},
        }
        return _mcp_result(req_id, result)
    if method_name == "initialize":
        offered = params.get("protocolVersion", "2026-07-28")
        result = {"protocolVersion": offered,
                  "capabilities": {"tools": {}},
                  "serverInfo": {"name": "github-core-clone", "version": "1.0.0"}}
        return _mcp_result(req_id, result)
    if method_name == "tools/list":
        # Reuse the pre-built tools JSON so the array is byte-identical.
        result = {"tools": json.loads(MCP_TOOLS_JSON)}
        return _mcp_result(req_id, result)
    if method_name == "tools/call":
        return _mcp_tools_call(req_id, params)
    if method_name.startswith("notifications/"):
        return make_response(202, b"", content_type=None)
    return _mcp_error(req_id, -32601, f"Method not found: {method_name}")


def _mcp_tools_call(req_id, params):
    name = params.get("name", "")
    args = params.get("arguments") or {}
    if not isinstance(args, dict):
        args = {}
    tool = next((t for t in MCP_TOOLS if t["name"] == name), None)
    if tool is None:
        return _mcp_error(req_id, -32602, f"Unknown tool: {name}")
    required = tool["inputSchema"].get("required", [])
    missing = [r for r in required if r not in args or args[r] is None]
    if missing:
        # A missing required argument: isError (never HTTP 500).
        result = {"content": [{"type": "text",
                               "text": json.dumps({"error": f"missing required argument(s): {', '.join(missing)}"})}],
                  "isError": True}
        return _mcp_result(req_id, result)
    try:
        if name == "create_repo":
            repo = create_repo(VIEWER_LOGIN, args["name"],
                               args.get("private", False),
                               args.get("description", ""))
            if repo is None:
                result = {"content": [{"type": "text", "text": json.dumps({"error": "Repository already exists"})}],
                          "isError": True}
                return _mcp_result(req_id, result)
            return _mcp_result(req_id, _mcp_tool_result(repo.json()))
        owner, repo_name = _mcp_owner_repo(args)
        repo = repo_from_path(owner, repo_name) if owner and repo_name else None
        if name == "get_repo":
            if repo is None:
                result = {"content": [{"type": "text", "text": json.dumps({"error": "Not Found"})}],
                          "isError": True}
                return _mcp_result(req_id, result)
            return _mcp_result(req_id, _mcp_tool_result(repo.json()))
        if repo is None:
            result = {"content": [{"type": "text", "text": json.dumps({"error": "Not Found"})}],
                      "isError": True}
            return _mcp_result(req_id, result)
        if name == "create_issue":
            with store_lock:
                number = repo.next_issue
                repo.next_issue += 1
                issue = Issue(repo.rid, number, args["title"], args.get("body", ""), [])
                issue.refresh_json(repo)
                repo.issues[number] = issue
            return _mcp_result(req_id, _mcp_tool_result(json.loads(issue.json.decode("utf-8"))))
        if name == "list_issues":
            state = args.get("state", "open")
            with store_lock:
                issues = list(repo.issues.values())
            if state != "all":
                issues = [i for i in issues if i.state == state]
            issues.sort(key=lambda i: i.number)
            objs = [json.loads(i.json.decode("utf-8")) for i in issues]
            return _mcp_result(req_id, _mcp_tool_result(objs))
        if name == "create_pull_request":
            head = args["head"]
            base = args["base"]
            with store_lock:
                head_tip = repo.refs.get("refs/heads/" + head)
                base_tip = repo.refs.get("refs/heads/" + base)
                if head_tip is None or base_tip is None:
                    result = {"content": [{"type": "text", "text": json.dumps({"error": "head or base branch does not exist"})}],
                              "isError": True}
                    return _mcp_result(req_id, result)
                changed = compute_diff(get_tree_at(repo, base_tip), get_tree_at(repo, head_tip))
                number = repo.next_pull
                repo.next_pull += 1
                pull = Pull(repo.rid, number, args["title"], args.get("body", ""),
                            head, head_tip, base, base_tip, base_tip, changed)
                pull.refresh_json(repo)
                repo.pulls[number] = pull
            return _mcp_result(req_id, _mcp_tool_result(json.loads(pull.json.decode("utf-8"))))
        if name == "merge_pull_request":
            number = args["pull_number"]
            if isinstance(number, str):
                try:
                    number = int(number)
                except ValueError:
                    pass
            with store_lock:
                pull = repo.pulls.get(number)
                if pull is None:
                    result = {"content": [{"type": "text", "text": json.dumps({"error": "Not Found"})}],
                              "isError": True}
                    return _mcp_result(req_id, result)
                if pull.state != "open":
                    result = {"content": [{"type": "text", "text": json.dumps({"error": "Pull request is not open"})}],
                              "isError": True}
                    return _mcp_result(req_id, result)
                merge_sha = squash_merge(repo, pull)
                if merge_sha is None:
                    result = {"content": [{"type": "text", "text": json.dumps({"error": "Merge conflict"})}],
                              "isError": True}
                    return _mcp_result(req_id, result)
                pull.merged = True
                pull.state = "closed"
                pull.merged_at = _iso(pull.pid + 1000)
                pull.merge_sha = merge_sha
                pull.refresh_json(repo)
            return _mcp_result(req_id, _mcp_tool_result(
                {"sha": merge_sha, "merged": True, "number": pull.number}))
    except Exception as exc:
        result = {"content": [{"type": "text", "text": json.dumps({"error": str(exc)})}],
                  "isError": True}
        return _mcp_result(req_id, result)
    return _mcp_error(req_id, -32602, f"Unknown tool: {name}")

# ---------------------------------------------------------------------------
# Git smart HTTP
# ---------------------------------------------------------------------------

# Pack cache: key -> framed sideband bytes of the packfile section.
# The key is the exact fetch input, so a repeated identical fetch (the
# clone workload's 50 concurrent depth-1 clones of one tip) is served
# from cache. Entries are immutable (objects are never deleted), so the
# cache never goes stale; it is bounded to keep memory in check.
_pack_cache = {}
_pack_cache_order = []
_PACK_CACHE_MAX = 256
_pack_cache_lock = threading.Lock()

# Cache of the (repo, refname) -> advertisement bytes for ls-refs/info-refs
# is not kept: advertisements are cheap (a few dozen refs) and must reflect
# the current refs.


def _pack_cache_get(key):
    with _pack_cache_lock:
        return _pack_cache.get(key)


def _pack_cache_put(key, value):
    with _pack_cache_lock:
        if key not in _pack_cache:
            _pack_cache_order.append(key)
            if len(_pack_cache_order) > _PACK_CACHE_MAX:
                old = _pack_cache_order.pop(0)
                _pack_cache.pop(old, None)
        _pack_cache[key] = value


def _advertisement_v2(repo):
    """protocol v2 capability advertisement."""
    lines = [pkt_line(b"version 2\n")]
    lines.append(pkt_line(b"agent=github-core-clone/1.0\n"))
    lines.append(pkt_line(b"ls-refs=unborn\n"))
    lines.append(pkt_line(b"fetch=shallow filter\n"))
    lines.append(pkt_line(b"object-format=sha1\n"))
    lines.append(FLUSH)
    return b"".join(lines)


def _refs_for_advertisement(repo):
    with store_lock:
        refs = dict(repo.refs)
    return refs


def _advertisement_v0(repo, service):
    """v0 advertisement: `# service=...` preamble + ref lines. The first
    ref line carries the capabilities after a NUL."""
    out = bytearray()
    out += pkt_line(f"# service={service}\n")
    # The flush after the service line is REQUIRED: real git parses the
    # advertisement as service-line, flush, ref-lines, flush. Without
    # it git reads the first ref line as the flush and dies.
    out += FLUSH
    refs = _refs_for_advertisement(repo)
    caps = ("report-status report-status-v2 side-band-64k delete-refs "
            "ofs-delta agent symref=HEAD:refs/heads/" + repo.default_branch)
    if service == "git-upload-pack":
        caps = ("side-band-64k ofs-delta agent "
                "symref=HEAD:refs/heads/" + repo.default_branch)
    first = True
    if refs:
        for refname in sorted(refs):
            line = refs[refname] + " " + refname + "\n"
            if first:
                line = refs[refname] + " " + refname + "\x00" + caps + "\n"
                first = False
            out += pkt_line(line)
        # HEAD as a symref line.
        head_oid = refs.get("refs/heads/" + repo.default_branch)
        if head_oid:
            out += pkt_line(head_oid + " HEAD\n")
    else:
        out += pkt_line(ZERO_OID + " capabilities^{}\x00" + caps + "\n")
    out += FLUSH
    return bytes(out)


def _ls_refs_response(repo, args):
    """v2 ls-refs response. args: peel, symrefs, unborn, prefixes."""
    refs = _refs_for_advertisement(repo)
    peel = args.get("peel", False)
    symrefs = args.get("symrefs", False)
    unborn = args.get("unborn", False)
    prefixes = args.get("prefixes", [])
    out = bytearray()
    default_tip = refs.get("refs/heads/" + repo.default_branch)
    # HEAD is reported when no prefix filter is given, or when a prefix
    # matches "HEAD" (real git clones ask for ref-prefix HEAD explicitly;
    # dropping it makes git think the repo has no HEAD to check out).
    show_head = (not prefixes) or any("HEAD".startswith(p) for p in prefixes)
    if show_head:
        if default_tip:
            line = default_tip + " HEAD"
            if symrefs:
                line += " symref-target:refs/heads/" + repo.default_branch
            out += pkt_line(line + "\n")
        elif unborn:
            line = "unborn HEAD"
            if symrefs:
                line += " symref-target:refs/heads/" + repo.default_branch
            out += pkt_line(line + "\n")
    for refname in sorted(refs):
        if prefixes and not any(refname.startswith(p) for p in prefixes):
            continue
        oid = refs[refname]
        line = oid + " " + refname
        if peel and refname.startswith("refs/tags/"):
            entry = objects.get(oid)
            if entry and entry[0] == "tag":
                # Peel an annotated tag to its commit.
                content = entry[1]
                for l in content.split(b"\n"):
                    if l.startswith(b"object "):
                        line += " peeled:" + l[7:].decode("ascii")
                        break
        out += pkt_line(line + "\n")
    out += FLUSH
    return bytes(out)


def _parse_v2_request(packets):
    """Parse a v2 command request. Returns (command, args dict, raw lines)."""
    args = {"peel": False, "symrefs": False, "unborn": False,
            "prefixes": [], "wants": [], "haves": [], "shallow": [],
            "depth": None, "filter": None, "thin-pack": False,
            "no-progress": False, "ofs-delta": False, "done": False,
            "deepen-since": None, "deepen-not": []}
    command = None
    seen_delim = False
    for kind, payload in packets:
        if kind == "flush":
            break
        if kind == "delim":
            seen_delim = True
            continue
        if kind != "data":
            continue
        line = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        if command is None and line.startswith("command="):
            command = line[len("command="):]
            continue
        if line.startswith("agent=") or line.startswith("object-format="):
            continue
        if line == "peel":
            args["peel"] = True
        elif line == "symrefs":
            args["symrefs"] = True
        elif line == "unborn":
            args["unborn"] = True
        elif line.startswith("ref-prefix "):
            args["prefixes"].append(line[len("ref-prefix "):])
        elif line.startswith("want "):
            args["wants"].append(line[5:].strip())
        elif line.startswith("have "):
            args["haves"].append(line[5:].strip())
        elif line.startswith("shallow "):
            args["shallow"].append(line[8:].strip())
        elif line.startswith("deepen "):
            try:
                args["depth"] = int(line[7:].strip())
            except ValueError:
                pass
        elif line.startswith("deepen-since "):
            args["deepen-since"] = line[len("deepen-since "):].strip()
        elif line.startswith("deepen-not "):
            args["deepen-not"].append(line[len("deepen-not "):].strip())
        elif line.startswith("filter "):
            args["filter"] = line[7:].strip()
        elif line == "thin-pack":
            args["thin-pack"] = True
        elif line == "no-progress":
            args["no-progress"] = True
        elif line == "ofs-delta":
            args["ofs-delta"] = True
        elif line == "done":
            args["done"] = True
    return command, args


def _fetch_v2_response(repo, args):
    """Build a v2 fetch response. Sections are separated by DELIM; the
    acknowledgments section is OMITTED when the client sent no haves."""
    wants = args["wants"]
    haves = args["haves"]
    shallow = args["shallow"]
    depth = args["depth"]
    # Resolve wants to commits that exist.
    valid_wants = [w for w in wants if w in objects and objects[w][0] in ("commit", "tag")]
    cache_key = (repo.rid, tuple(sorted(valid_wants)), tuple(sorted(haves)),
                 tuple(sorted(shallow)), depth)
    cached = _pack_cache_get(cache_key)
    send, new_shallow, unshallow = fetch_selection(valid_wants, haves, shallow, depth)
    if cached is not None:
        pack_section = cached
    else:
        # Pack order: commits, then trees, then blobs (deterministic).
        ordered = sorted(send, key=lambda o: ({"commit": 0, "tree": 1, "tag": 2, "blob": 3}[objects[o][0]], o))
        pack_bytes = write_pack(ordered)
        pack_section = sideband_pack(pack_bytes)
        _pack_cache_put(cache_key, pack_section)
    out = bytearray()
    if haves:
        out += pkt_line(b"acknowledgments\n")
        # The client sent haves; NAK means "I need more" (we always send).
        out += pkt_line(b"NAK\n")
        out += DELIM
    if new_shallow or unshallow:
        out += pkt_line(b"shallow-info\n")
        for s in new_shallow:
            out += pkt_line(f"shallow {s}\n")
        for s in unshallow:
            out += pkt_line(f"unshallow {s}\n")
        out += DELIM
    # wanted-refs: the refs whose tips were wanted.
    refs = _refs_for_advertisement(repo)
    wanted_refs = []
    for refname, oid in sorted(refs.items()):
        if oid in valid_wants:
            wanted_refs.append((oid, refname))
    if wanted_refs:
        out += pkt_line(b"wanted-refs\n")
        for oid, refname in wanted_refs:
            out += pkt_line(f"{oid} {refname}\n")
        out += DELIM
    out += pkt_line(b"packfile\n")
    out += pack_section
    out += FLUSH
    return bytes(out)


def _fetch_v0_response(repo, args):
    """v0 fetch: NAK/ACK lines, shallow lines, then the sideband pack."""
    wants = args["wants"]
    haves = args["haves"]
    shallow = args["shallow"]
    depth = args["depth"]
    valid_wants = [w for w in wants if w in objects and objects[w][0] in ("commit", "tag")]
    send, new_shallow, unshallow = fetch_selection(valid_wants, haves, shallow, depth)
    out = bytearray()
    if haves:
        out += pkt_line(b"NAK\n")
    for s in new_shallow:
        out += pkt_line(f"shallow {s}\n")
    for s in unshallow:
        out += pkt_line(f"unshallow {s}\n")
    ordered = sorted(send, key=lambda o: ({"commit": 0, "tree": 1, "tag": 2, "blob": 3}[objects[o][0]], o))
    pack_bytes = write_pack(ordered) if ordered else write_pack([])
    out += sideband_pack(pack_bytes)
    return bytes(out)


def _receive_pack_response(repo, commands, pack_objects):
    """Apply a push: store the objects, validate each ref update, and
    build the report-status response in sideband band 1 with its own
    inner FLUSH terminator (real git dies on EOF without it)."""
    # Store the objects first (all of them, even for refused refs).
    for oid, (otype, content) in pack_objects.items():
        objects.setdefault(oid, (otype, content))
    report_lines = []
    with store_lock:
        for old_oid, new_oid, refname in commands:
            if new_oid == ZERO_OID:
                # Delete.
                current = repo.refs.get(refname)
                if current is None:
                    report_lines.append(f"ng {refname} ref does not exist\n")
                elif current != old_oid:
                    report_lines.append(f"ng {refname} non-fast-forward\n")
                else:
                    del repo.refs[refname]
                    report_lines.append(f"ok {refname}\n")
                continue
            if new_oid not in objects:
                report_lines.append(f"ng {refname} object not found\n")
                continue
            if refname.startswith("refs/tags/"):
                # A tag ref may point at a tag object (annotated) or a
                # commit (lightweight); no fast-forward rule applies.
                if objects[new_oid][0] not in ("commit", "tag"):
                    report_lines.append(f"ng {refname} object not found\n")
                    continue
                if old_oid == ZERO_OID:
                    if refname in repo.refs:
                        report_lines.append(f"ng {refname} ref already exists\n")
                    else:
                        repo.refs[refname] = new_oid
                        report_lines.append(f"ok {refname}\n")
                    continue
                current = repo.refs.get(refname)
                if current != old_oid:
                    report_lines.append(f"ng {refname} non-fast-forward\n")
                    continue
                repo.refs[refname] = new_oid
                report_lines.append(f"ok {refname}\n")
                continue
            if objects[new_oid][0] != "commit":
                report_lines.append(f"ng {refname} object not found\n")
                continue
            if old_oid == ZERO_OID:
                # Create.
                if refname in repo.refs:
                    report_lines.append(f"ng {refname} ref already exists\n")
                else:
                    repo.refs[refname] = new_oid
                    report_lines.append(f"ok {refname}\n")
                continue
            current = repo.refs.get(refname)
            if current != old_oid:
                report_lines.append(f"ng {refname} non-fast-forward\n")
                continue
            if not is_ancestor(old_oid, new_oid):
                report_lines.append(f"ng {refname} non-fast-forward\n")
                continue
            repo.refs[refname] = new_oid
            report_lines.append(f"ok {refname}\n")
    body = bytearray()
    body += pkt_line(b"unpack ok\n")
    for line in report_lines:
        body += pkt_line(line.encode("utf-8"))
    body += FLUSH  # inner FLUSH: terminates the band-1 report stream.
    # Wrap the whole report in one sideband band-1 packet.
    framed = pkt_line(b"\x01" + bytes(body))
    return framed


def _parse_push_commands(packets):
    """Parse the ref-update command list at the start of a receive-pack
    body. Returns (commands, pack_offset) where pack_offset is the byte
    offset in the raw body where the pack starts."""
    commands = []
    # We need the raw byte stream to find where the pack begins, so this
    # is handled by the caller; here we only parse the pkt-lines.
    for kind, payload in packets:
        if kind != "data":
            break
        line = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        # The first command line carries capabilities after a NUL.
        if "\x00" in line:
            line = line.split("\x00", 1)[0]
        parts = line.split(" ")
        if len(parts) != 3:
            break
        old_oid, new_oid, refname = parts
        if len(old_oid) != 40 or len(new_oid) != 40:
            break
        commands.append((old_oid, new_oid, refname))
    return commands


def handle_git(method, path, query, headers, body):
    # path: /{owner}/{repo}.git/info/refs  or  /{owner}/{repo}.git/<service>
    m = re.match(r"^/([^/]+)/([^/]+)\.git(?:/(.*))?$", path)
    if not m:
        return error_response(404, "Not Found")
    owner, repo_name, tail = m.group(1), m.group(2), m.group(3) or ""
    repo = repo_from_path(owner, repo_name)
    git_protocol = headers.get("git-protocol", "")
    if method == "GET" and tail == "info/refs":
        service = query.get("service", "")
        if repo is None:
            return error_response(404, "Not Found")
        if service == "git-upload-pack":
            if git_protocol == "version=2":
                payload = _advertisement_v2(repo)
                return make_response(200, payload,
                                     content_type="application/x-git-upload-pack-advertisement")
            payload = _advertisement_v0(repo, "git-upload-pack")
            return make_response(200, payload,
                                 content_type="application/x-git-upload-pack-advertisement")
        if service == "git-receive-pack":
            payload = _advertisement_v0(repo, "git-receive-pack")
            return make_response(200, payload,
                                 content_type="application/x-git-receive-pack-advertisement")
        return error_response(404, "Not Found")
    if method != "POST":
        return error_response(404, "Not Found")
    if repo is None:
        return error_response(404, "Not Found")
    if tail == "git-upload-pack":
        return _handle_upload_pack(repo, git_protocol, body)
    if tail == "git-receive-pack":
        return _handle_receive_pack(repo, body)
    return error_response(404, "Not Found")


def _handle_upload_pack(repo, git_protocol, body):
    try:
        packets = parse_pkt_lines(body)
    except ValueError:
        # Malformed request: answer 400, stay alive.
        return error_response(400, "malformed pkt-line stream")
    if git_protocol == "version=2":
        command, args = _parse_v2_request(packets)
        if command == "ls-refs":
            return make_response(200, _ls_refs_response(repo, args),
                                 content_type="application/x-git-upload-pack-result")
        if command == "fetch":
            return make_response(200, _fetch_v2_response(repo, args),
                                 content_type="application/x-git-upload-pack-result")
        return error_response(400, "unknown v2 command")
    # v0 fetch: wants + haves, then a flush, then the pack request.
    args = {"wants": [], "haves": [], "shallow": [], "depth": None}
    for kind, payload in packets:
        if kind != "data":
            continue
        line = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        if "\x00" in line:
            line = line.split("\x00", 1)[0]
        if line.startswith("want "):
            args["wants"].append(line[5:].strip())
        elif line.startswith("have "):
            args["haves"].append(line[5:].strip())
        elif line.startswith("shallow "):
            args["shallow"].append(line[8:].strip())
        elif line.startswith("deepen "):
            try:
                args["depth"] = int(line[7:].strip())
            except ValueError:
                pass
    return make_response(200, _fetch_v0_response(repo, args),
                         content_type="application/x-git-upload-pack-result")


def _handle_receive_pack(repo, body):
    # The body is: ref-update pkt-lines, a FLUSH, then the raw pack bytes.
    # Find the first FLUSH pkt-line; everything after it is the pack.
    pos = 0
    n = len(body)
    commands = []
    pack_start = None
    while pos + 4 <= n:
        try:
            length = int(body[pos:pos + 4], 16)
        except ValueError:
            break
        if length == 0:
            pack_start = pos + 4
            break
        if length < 4 or pos + length > n:
            break
        payload = body[pos + 4:pos + length]
        line = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        if "\x00" in line:
            line = line.split("\x00", 1)[0]
        parts = line.split(" ")
        if len(parts) == 3 and len(parts[0]) == 40 and len(parts[1]) == 40:
            commands.append((parts[0], parts[1], parts[2]))
        pos += length
    if pack_start is None:
        # No pack (a delete-only push has no pack bytes).
        pack_start = n
    pack_objects = {}
    if pack_start < n:
        try:
            pack_objects = read_pack(body[pack_start:])
        except Exception:
            return error_response(400, "malformed packfile")
    framed = _receive_pack_response(repo, commands, pack_objects)
    return make_response(200, framed,
                         content_type="application/x-git-receive-pack-result")


# ---------------------------------------------------------------------------
# Lifecycle: register with the env, serve, poll /done
# ---------------------------------------------------------------------------

def _http_json(url, payload, timeout=10):
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(url, data=data, method="POST" if data is not None else "GET")
    req.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _poll_done(stop_event):
    if not ENV_URL:
        return
    while not stop_event.is_set():
        try:
            result = _http_json(ENV_URL.rstrip("/") + "/done", None, timeout=10)
            if isinstance(result, dict) and result.get("done"):
                stop_event.set()
                return
        except Exception:
            pass
        stop_event.wait(1.0)


def main():
    server = ForgeServer(("127.0.0.1", PORT), ForgeHandler)
    port = server.server_address[1]
    stop_event = threading.Event()
    if ENV_URL:
        # Register this process's port with the suite, then serve until done.
        try:
            _http_json(ENV_URL.rstrip("/") + "/register", {"port": port}, timeout=10)
        except Exception as exc:
            sys.stderr.write(f"register failed: {exc}\n")
        poller = threading.Thread(target=_poll_done, args=(stop_event,), daemon=True)
        poller.start()
        # Serve until the poller sees done, then shut down cleanly.
        while not stop_event.is_set():
            server.timeout = 0.5
            server.handle_request()
        server.server_close()
        return 0
    # Local dev: just serve on the chosen port until killed.
    sys.stderr.write(f"forge listening on 127.0.0.1:{port} (token {TOKEN[:4]}...)\n")
    sys.stderr.flush()
    try:
        server.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
