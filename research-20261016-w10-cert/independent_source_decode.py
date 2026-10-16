"""Independent extraction of the readable source carried by w10_expand.

This uses neither bundle.py nor lzss_source.py.  It checks the uploaded
literal chunks, byte stream, overlapping copy operations, and exact identity
of the decoded body inside the accompanying readable source.  It supplies
no mathematical evidence beyond that identity; Lean and nanoda must check
the exact upload separately.
"""
from pathlib import Path
import argparse, hashlib, json, re


def digest(data):
    return hashlib.sha256(data).hexdigest()


def extract_command(command):
    expected, size = int(command[1]), int(command[2])
    assert 0 < expected < 100_000_000 and 0 < size < 100_000_000
    alphabet = bytes(c for c in range(33, 127) if c not in [34, 92])
    literals = re.findall(rb'"([^"\\\r\n]*)"', command[3])
    assert len(literals) == (size + 255) // 256
    stream = bytearray()
    for literal in literals:
        word = 0
        for char in literal:
            word = 92 * word + alphabet.index(char)
        count = min(256, size - len(stream))
        assert word < 256 ** count, 'A literal exceeds its declared byte length'
        stream.extend(word.to_bytes(count, 'little'))
    assert len(stream) == size
    result = bytearray()
    cursor = 0
    copies = literals_count = 0
    while len(result) < expected:
        assert cursor < len(stream), 'Missing token flags'
        flags = stream[cursor]
        cursor += 1
        for bit in range(8):
            if len(result) == expected:
                break
            if flags & (1 << bit):
                assert cursor + 3 <= len(stream), 'Truncated copy token'
                distance = int.from_bytes(stream[cursor:cursor+2], 'little') + 1
                count = stream[cursor+2] + 3
                cursor += 3
                assert distance <= len(result) and len(result) + count <= expected
                for _ in range(count):
                    result.append(result[len(result)-distance])
                copies += 1
            else:
                assert cursor < len(stream), 'Truncated literal token'
                result.append(stream[cursor])
                cursor += 1
                literals_count += 1
    assert len(result) == expected and cursor == len(stream), 'Unused compressed bytes'
    result.decode('utf8', errors='strict')
    return bytes(result), {'decoded_bytes': expected, 'decoded_sha256': digest(result),
                           'command_sha256': digest(command[0]), 'compressed_bytes': size,
                           'source_chunks': len(literals), 'copy_tokens': copies,
                           'literal_tokens': literals_count}


def extract(source):
    pattern = rb'^w10_expand[ \t]+([0-9]+)[ \t]+([0-9]+)[ \t]+\[((?:\s*"[^"\\\r\n]*"\s*,?)*)\][ \t]*\r?\n'
    commands = list(re.finditer(pattern, source, re.M))
    assert commands, 'Expected at least one source expansion command'
    bodies = []
    blocks = []
    for command in commands:
        body, metadata = extract_command(command)
        bodies.append(body)
        blocks.append(metadata)
    result = b''.join(bodies)
    statistics = {key: sum(b[key] for b in blocks) for key in
                  ['decoded_bytes', 'compressed_bytes', 'source_chunks', 'copy_tokens', 'literal_tokens']}
    statistics.update(source_expansion_commands=len(blocks), blocks=blocks)
    return result, statistics


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('upload', type=Path)
    parser.add_argument('readable', type=Path)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    upload = args.upload.read_bytes()
    readable = args.readable.read_bytes()
    body, statistics = extract(upload)
    assert readable.count(body) == 1, 'Decoded body is not one exact region of readable source'
    body_hash = digest(body)
    if args.manifest:
        manifest = json.loads(args.manifest.read_bytes())
        assert manifest['expanded_base_sha256'] == body_hash
        assert manifest['expanded_base_bytes'] == len(body)
        assert manifest['expanded_source_sha256'] == digest(readable)
        assert manifest['source_sha256'] == digest(upload)
        assert manifest['source_block_count'] == statistics['source_expansion_commands']
        for actual, expected in zip(statistics['blocks'], manifest['source_blocks'], strict=True):
            for key in ['decoded_bytes', 'decoded_sha256', 'compressed_bytes', 'command_sha256']:
                assert actual[key] == expected[key], ('Source block metadata mismatch', key)
    assert args.upload.read_bytes() == upload and args.readable.read_bytes() == readable
    receipt = {'passed': True, 'scope': __doc__, **statistics,
               'upload': str(args.upload), 'upload_sha256': digest(upload),
               'readable': str(args.readable), 'readable_sha256': digest(readable),
               'decoded_body_sha256': body_hash,
               'script_sha256': digest(Path(__file__).read_bytes()),
               'decoded_body_exact_readable_region': True,
               'lean_verification_claimed': False, 'nanoda_verification_claimed': False}
    args.output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf8')
    print(json.dumps({k: receipt[k] for k in ['passed', 'decoded_bytes', 'compressed_bytes', 'decoded_body_sha256']}))


if __name__ == '__main__':
    main()
