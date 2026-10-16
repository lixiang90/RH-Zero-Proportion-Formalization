"""Conservative compressed-source boundaries at complete scope commands.

Comments and strings are masked.  A cut is permitted only after an entire
column-zero namespace/section/end command with no enclosing delimiter.
Declarations and proofs are never split by a guessed indentation boundary.
"""
from pathlib import Path
import re, sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
from bundle_gram_defect_solution import code_mask


def scope_blocks(raw, target=32768):
    if not __debug__:
        raise RuntimeError('Source block assertions must remain enabled')
    assert target > 0
    text = raw.decode('utf8', errors='strict')
    masked = code_mask(text)
    identifier = r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*'
    scope = re.compile(r'(?:namespace|(?:noncomputable )?section|end)(?:\s+'+identifier+r')?')
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    stack = []
    blocks = []
    start = offset = bytes_since_cut = 0
    for original, line in zip(text.splitlines(keepends=True), masked.splitlines(keepends=True), strict=True):
        for char in line:
            if char in '([{⟨':
                stack.append(char)
            elif char in pairs:
                assert stack and stack[-1] == pairs[char], ('Unsupported delimiter syntax', offset, char)
                stack.pop()
        offset += len(line)
        bytes_since_cut += len(original.encode('utf8'))
        if not stack and scope.fullmatch(line.rstrip()) and bytes_since_cut >= target:
            blocks.append(text[start:offset].encode('utf8'))
            start = offset
            bytes_since_cut = 0
    assert not stack, 'Unclosed source delimiter'
    if start < len(text):
        blocks.append(text[start:].encode('utf8'))
    assert blocks and all(blocks) and b''.join(blocks) == raw
    return blocks
