#!/usr/bin/env python3
"""Read or deliberately damage a fixture's *logical* receipt byte stream.

CRASH.md uses this to test the record codec independently of the disk layout.
`flip` damages the selected physical block. `cut` and `remove` emit a legacy byte
file, which the normal append path migrates; they never fabricate an index checksum.
This is a fault-injection helper, never an application recovery implementation.
"""
import pathlib
import sys

CAPACITY = 65536


def selected(vault):
    path = pathlib.Path(vault) / ".obend" / "log"
    prefix = path.read_bytes()[:256]
    if not prefix.startswith(b"obend-segments "):
        return path, None
    fields = prefix.decode().split()
    return path, (path.parent / "log-segments" / fields[2], int(fields[3]))


def read(vault):
    path, layout = selected(vault)
    if layout is None:
        return path.read_bytes()
    directory, active = layout
    blocks = []
    for i in range(active + 1):
        path = directory / str(i)
        if not path.exists():
            if i == active and (i == 0 or len(blocks[-1]) == CAPACITY):
                break
            raise ValueError(f"missing interior log block: {path}")
        data = path.read_bytes()
        if len(data) > CAPACITY or (i < active and len(data) != CAPACITY):
            raise ValueError(f"invalid log block size: {path}")
        blocks.append(data)
    return b"".join(blocks)


def write(vault, data):
    path, layout = selected(vault)
    if layout is None:
        path.write_bytes(data)
        return
    # Fault tests may change the log's logical length. Use the legacy codec as the interchange
    # format, then let the next normal append migrate it; don't fabricate a checksummed index.
    path.write_bytes(data)


def main():
    op, vault, *args = sys.argv[1:]
    data = read(vault)
    if op == "cat":
        sys.stdout.buffer.write(data)
    elif op == "cut":
        write(vault, data[:int(args[0])])
    elif op == "remove":
        a, b = map(int, args)
        write(vault, data[:a] + data[b:])
    elif op == "flip":
        k = int(args[0])
        path, layout = selected(vault)
        if layout is None:
            target, offset = path, k
        else:
            target, offset = layout[0] / str(k // CAPACITY), k % CAPACITY
        block = bytearray(target.read_bytes())
        block[offset] ^= 1
        target.write_bytes(block)
    else:
        raise SystemExit(f"unknown operation: {op}")


if __name__ == "__main__":
    main()
