"""The Jupyter wire protocol: HMAC-signed multipart messages.

This is the whole of the protocol on the wire (Jupyter's messaging spec, version
5.3): a message on a ZeroMQ socket is

    [identities..., b"<IDS|MSG>", signature, header, parent_header, metadata, content, buffers...]

where ``signature`` is the lowercase hex HMAC of the four JSON frames in order, with
the connection file's key, if there is one.  Nothing here needs Jupyter: only
``hashlib``, ``hmac`` and ``json``.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Iterable, Sequence

DELIMITER = b"<IDS|MSG>"
PROTOCOL_VERSION = "5.3"

_DIGESTS = {
    "hmac-sha256": hashlib.sha256,
    "hmac-sha1": hashlib.sha1,
    "hmac-sha512": hashlib.sha512,
    "hmac-md5": hashlib.md5,
}


class WireError(Exception):
    """A malformed or unauthenticated message."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def json_pack(obj: Any) -> bytes:
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def json_unpack(data: bytes) -> Any:
    if not data:
        return {}
    return json.loads(data.decode("utf-8"))


@dataclass
class Message:
    header: dict
    content: dict
    parent_header: dict = field(default_factory=dict)
    metadata: dict = field(default_factory=dict)
    buffers: list[bytes] = field(default_factory=list)
    identities: list[bytes] = field(default_factory=list)

    @property
    def msg_type(self) -> str:
        return self.header.get("msg_type", "")

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"Message({self.msg_type!r}, {self.content!r})"


class Session:
    """Signs and parses messages for one kernel (or client)."""

    def __init__(self, key: str = "", scheme: str = "hmac-sha256", session_id: str | None = None):
        self.key = key.encode("utf-8") if isinstance(key, str) else (key or b"")
        try:
            self.digestmod = _DIGESTS[scheme or "hmac-sha256"]
        except KeyError:
            raise WireError(f"unsupported signature_scheme {scheme!r}") from None
        self.session_id = session_id or uuid.uuid4().hex

    def sign(self, *frames: bytes) -> str:
        if not self.key:
            return ""
        mac = hmac.new(self.key, digestmod=self.digestmod)
        for frame in frames:
            mac.update(frame)
        return mac.hexdigest()

    def header(self, msg_type: str, username: str = "kernel") -> dict:
        return {
            "msg_id": uuid.uuid4().hex,
            "username": username,
            "session": self.session_id,
            "date": utc_now(),
            "msg_type": msg_type,
            "version": PROTOCOL_VERSION,
        }

    def serialize(
        self,
        msg_type: str,
        content: dict | None = None,
        *,
        parent: dict | None = None,
        metadata: dict | None = None,
        buffers: Iterable[bytes] = (),
        identities: Sequence[bytes] = (),
        header: dict | None = None,
    ) -> list[bytes]:
        header = header or self.header(msg_type)
        frames = [json_pack(header), json_pack(parent or {}), json_pack(metadata or {}),
                  json_pack(content or {})]
        signature = self.sign(*frames)
        return [*identities, DELIMITER, signature.encode("ascii"), *frames, *buffers]

    def deserialize(self, frames: Sequence[bytes], *, verify: bool = True) -> Message:
        try:
            split = list(frames).index(DELIMITER)
        except ValueError:
            raise WireError("no <IDS|MSG> delimiter") from None
        if len(frames) < split + 6:
            raise WireError("truncated message")
        signature = frames[split + 1]
        signed = list(frames[split + 2:split + 6])
        if verify:
            expected = self.sign(*signed)
            if not hmac.compare_digest(signature.decode("ascii", "replace"), expected):
                raise WireError("bad signature")
        header, parent, metadata, content = (json_unpack(f) for f in signed)
        return Message(
            header=header,
            content=content,
            parent_header=parent,
            metadata=metadata,
            buffers=list(frames[split + 6:]),
            identities=list(frames[:split]),
        )


def iopub_topic(msg_type: str) -> bytes:
    return b"kernel." + msg_type.encode("utf-8")
