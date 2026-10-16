"""Expand w10_expand bodies to readable UTF-8 Lean for independent review.

This reader intentionally does not import the compressor or any certificate
generator.  It is a convenience for source inspection; neither it nor a
roundtrip receipt replaces Lean's kernel or the independent proof replay.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ALPHABET = ''.join(chr(c) for c in range(33, 127) if c not in (34, 92))
DIGITS = {ch: n for n, ch in enumerate(ALPHABET)}
COMMAND = re.compile(r'\bw10_expand\s+(\d+)\s+(\d+)\s*\['
                     r'((?:\s*"[^"\\]*"\s*,?\s*)*)\]')


def decode_command(expected, size, literals):
    strings = re.findall(r'"([^"\\]*)"', literals)
    if len(strings) != (size + 255) // 256:
        raise ValueError('wrong compressed chunk count')
    packed = bytearray()
    for string in strings:
        number = 0
        for ch in string:
            if ch not in DIGITS:
                raise ValueError('non-alphabet digit in compressed source')
            number = number * 92 + DIGITS[ch]
        count = min(256, size - len(packed))
        if number.bit_length() > 8 * count:
            raise ValueError('compressed chunk exceeds declared length')
        packed.extend(number.to_bytes(count, 'little'))
    raw = bytearray()
    cursor = 0
    while len(raw) < expected:
        if cursor >= len(packed):
            raise ValueError('truncated flag byte')
        flags = packed[cursor]
        cursor += 1
        for bit in range(8):
            if len(raw) == expected:
                break
            if flags >> bit & 1:
                if cursor + 3 > len(packed):
                    raise ValueError('truncated copy')
                distance = 1 + packed[cursor] + 256 * packed[cursor + 1]
                count = packed[cursor + 2] + 3
                cursor += 3
                if distance > len(raw) or len(raw) + count > expected:
                    raise ValueError('invalid copy range')
                for _ in range(count):
                    raw.append(raw[-distance])
            else:
                if cursor >= len(packed):
                    raise ValueError('truncated literal')
                raw.append(packed[cursor])
                cursor += 1
    if cursor != size:
        raise ValueError('unused compressed input')
    return bytes(raw)


def expand(source):
    bodies = []

    def replace(match):
        expected, size = map(int, match.group(1, 2))
        raw = decode_command(expected, size, match.group(3))
        text = raw.decode('utf8')
        bodies.append({'output_bytes': len(raw), 'compressed_bytes': size,
                       'output_sha256': hashlib.sha256(raw).hexdigest()})
        return text

    return COMMAND.sub(replace, source), bodies


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    if args.input.resolve() == args.output.resolve():
        raise ValueError('input and readable output must be different files')
    raw = args.input.read_bytes()
    text, bodies = expand(raw.decode('utf8'))
    if not bodies:
        raise ValueError('no literal w10_expand command found')
    output = text.encode('utf8')
    args.output.write_bytes(output)
    receipt = {'scope': 'Independent source decoding for inspection only; no proof verification.',
               'input': str(args.input), 'input_bytes': len(raw),
               'input_sha256': hashlib.sha256(raw).hexdigest(),
               'output': str(args.output), 'output_bytes': len(output),
               'output_sha256': hashlib.sha256(output).hexdigest(),
               'decoded_bodies': bodies}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf8')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
