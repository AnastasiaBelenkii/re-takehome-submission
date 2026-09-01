"""Deterministic, declaration-preserving call-zero tactic candidate."""

from __future__ import annotations

import re

TACTIC_CASCADE = "first | omega | norm_num | nlinarith | linarith | ring | aesop | simp_all"


def tactic_candidate(challenge: str) -> str | None:
    """Replace proof holes only; declaration text and numeric answers stay byte-identical."""
    candidate, count = re.subn(r"\bsorry\b", TACTIC_CASCADE, challenge)
    return candidate if count else None


def declaration_fingerprint(source: str) -> tuple[str, ...]:
    """Conservative normalized fingerprints for named declaration headers.

    This intentionally handles the challenge corpus' declarations rather than
    pretending to be a Lean parser. Final authority remains Comparator.
    """
    starts = list(re.finditer(
        r"(?m)^\s*(?:theorem|lemma|def|abbrev|opaque)\s+[A-Za-z_][A-Za-z0-9_'.]*\b",
        source,
    ))
    answer: list[str] = []
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(source)
        block = source[match.start():end]
        header, separator, _body = block.partition(":=")
        if not separator:
            header = block.partition(" where")[0]
        answer.append(" ".join(header.split()))
    return tuple(answer)


def declarations_unchanged(challenge: str, candidate: str) -> bool:
    """Legacy source-text comparison retained for audit replay only.

    This is deliberately not used as the live acceptance gate: definitionally
    equal Lean types can have different source spellings.
    """
    required = declaration_fingerprint(challenge)
    proposed = declaration_fingerprint(candidate)
    for fingerprint in required:
        match = re.match(
            r"(?:theorem|lemma|def|abbrev|opaque)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b",
            fingerprint,
        )
        if match is None:
            return False
        name = match.group(1)
        same_name = tuple(
            item for item in proposed
            if re.match(
                rf"(?:theorem|lemma|def|abbrev|opaque)\s+{re.escape(name)}"
                r"(?![A-Za-z0-9_'.])",
                item,
            )
        )
        if same_name != (fingerprint,):
            return False
    return True


def required_declarations_present(challenge: str, candidate: str) -> bool:
    """Require one declaration of every required name and compatible kind.

    This is only a completeness guard. It does not pretend to decide whether
    theorem statements are semantically equal; fresh Comparator verification
    is authoritative for every warm-Lean success.
    """
    compatible_kinds = {
        "theorem": {"theorem", "lemma"},
        "lemma": {"theorem", "lemma"},
        "def": {"def"},
        "abbrev": {"abbrev"},
        "opaque": {"opaque"},
    }

    def identity(fingerprint: str) -> tuple[str, str] | None:
        match = re.match(
            r"(theorem|lemma|def|abbrev|opaque)\s+"
            r"([A-Za-z_][A-Za-z0-9_'.]*)\b",
            fingerprint,
        )
        return (match.group(1), match.group(2)) if match else None

    proposed = [identity(item) for item in declaration_fingerprint(candidate)]
    for required_fingerprint in declaration_fingerprint(challenge):
        required = identity(required_fingerprint)
        if required is None:
            return False
        required_kind, required_name = required
        same_name = [item for item in proposed if item and item[1] == required_name]
        if len(same_name) != 1 or same_name[0][0] not in compatible_kinds[required_kind]:
            return False
    return True


def import_fingerprint(source: str) -> tuple[str, ...]:
    """Return normalized top-level imports in source order."""
    imports = []
    for match in re.finditer(r"(?m)^\s*import\s+([^\n]+)$", source):
        module_text = match.group(1).partition("--")[0]
        imports.append(" ".join(module_text.split()))
    return tuple(imports)


def imports_unchanged(challenge: str, candidate: str) -> bool:
    """Warm checking is sounder when final-file imports remain pristine."""
    return import_fingerprint(challenge) == import_fingerprint(candidate)


def canonicalize_imports(source: str) -> str:
    """Use the warm REPL's real `Mathlib` context in the submitted file too."""
    body = "\n".join(
        line for line in source.splitlines()
        if not line.lstrip().startswith("import ")
    ).lstrip("\n")
    return "import Mathlib\n\n" + body + ("\n" if body and not body.endswith("\n") else "")
