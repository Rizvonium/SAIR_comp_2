"""Subprocess wrapper around the C++ engine (``bin/acengine``).

The engine speaks JSON Lines on stdin/stdout.  ``stream`` yields results as
the engine finishes them, so callers can persist each one immediately
(crash safety: a killed batch loses at most the in-flight problems).
"""
from __future__ import annotations

import json
import os
import subprocess
import threading
from pathlib import Path
from typing import Iterable, Iterator

from .official import ROOT

BIN = ROOT / "bin" / "acengine"
DATA = ROOT / "data"


def ensure_built() -> Path:
    if not BIN.exists():
        subprocess.run(["make", "-C", str(ROOT), "bin/acengine"], check=True)
    return BIN


def default_endgame() -> Path | None:
    """Largest endgame table available in data/."""
    tables = sorted(DATA.glob("endgame_r*.bin"),
                    key=lambda p: int(p.stem.split("_r")[1]))
    return tables[-1] if tables else None


def _flags(params: dict) -> list[str]:
    out = []
    for k, v in params.items():
        if v is None or v is False:
            continue
        out += ["--" + k, "1" if v is True else str(v)]
    return out


def stream(cmd: str, records: Iterable[dict], params: dict | None = None,
           endgame: Path | None | str = "default", threads: int | None = None) -> Iterator[dict]:
    ensure_built()
    params = dict(params or {})
    if endgame == "default":
        endgame = default_endgame()
    if endgame:
        params["endgame"] = str(endgame)
    params["threads"] = threads or os.cpu_count() or 1
    proc = subprocess.Popen([str(BIN), cmd] + _flags(params), stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1)
    lines = [json.dumps(r) for r in records]

    def feed():
        try:
            for line in lines:
                proc.stdin.write(line + "\n")
            proc.stdin.close()
        except BrokenPipeError:
            pass

    stderr_chunks: list[str] = []

    def drain():
        for line in proc.stderr:
            stderr_chunks.append(line)

    t1 = threading.Thread(target=feed, daemon=True)
    t2 = threading.Thread(target=drain, daemon=True)
    t1.start()
    t2.start()
    try:
        for line in proc.stdout:
            line = line.strip()
            if line:
                yield json.loads(line)
    finally:
        if proc.poll() is None:
            proc.kill()
        proc.wait()
        t2.join(timeout=1)
    if proc.returncode not in (0, -9):
        raise RuntimeError("engine %s failed (%s): %s" % (cmd, proc.returncode, "".join(stderr_chunks)[-2000:]))


def run(cmd: str, records: Iterable[dict], **kw) -> list[dict]:
    return list(stream(cmd, records, **kw))


def build_endgame(radius: int) -> Path:
    ensure_built()
    out = DATA / f"endgame_r{radius}.bin"
    DATA.mkdir(exist_ok=True)
    if not out.exists():
        subprocess.run([str(BIN), "build-endgame", "--radius", str(radius), "--out", str(out)], check=True)
    return out
