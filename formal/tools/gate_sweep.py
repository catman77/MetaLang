#!/usr/bin/env python3
"""Сплошная ревизия покрытия гейтов корпуса WORLD-META формализацией MetaLang.

Читает `results/verdict.json` всех архивов, собирает полный список научных
гейтов, сопоставляет его с привязками в `final_certificate.json`, `PRD*.md`,
`ProofAudit.md` и `README.md`, классифицирует непокрытые гейты и печатает
сводку.

Использование:

    unzip -q docs/*.zip -d "$SCRATCH"          # архивы не трогаем в репозитории
    python3 formal/tools/gate_sweep.py "$SCRATCH" [--list]

Классы непокрытых гейтов:

* FORMALIZE — структурные утверждения, кандидаты в теоремы;
* NUM       — числовые пороги на популяции 32 миров (вне рамок по §3 PRD);
* DECL      — эпистемические декларации протокола («no claim is made …»);
* INST      — инструментальные аудиты аппарата (совпадение со скрытой
              истиной, перечисление, перемаркировка, replay);
* UNLABELED — версии v0.12–v0.14 нумеруют гейты голыми `S1`…`Sn` без
              описания в `verdict.json`; смысл читается из
              `run_experiment.py` и разбирается вручную.

Классификация — регулярными выражениями, то есть приблизительная. Она
служит для оценки объёма, а не для приёмки: приёмка идёт по §6 PRD.
"""

from __future__ import annotations

import glob
import json
import os
import re
import sys

NUM = re.compile(
    r"ge_0|le_0|_ge_|_le_|_rate$|_rate_|rate\b|mean|auc|_pct|accuracy|prevalence"
    r"|brier|r2|at_least|exactly_\w*\d|_\d+_of_\d+|twenty|five_|eight_|twelve"
    r"|three_new|two_new|depth3|_all_worlds",
    re.I,
)
DECL = re.compile(
    r"no_claim|does_not_claim|not_a_|is_not_a|is_metadata|only_under|conditional_on|analogy"
    r"|kept_as_distinct_formal_statuses|remains_conditional|does_not_imply_source"
    r"|is_not_an_exact_solver|not_metaphysical|epistemic|myth|superstition"
    r"|science_as_active",
    re.I,
)
INST = re.compile(
    r"matches_hidden|hidden_truth|_present$|_present_|enumerat|exhaust|replay"
    r"|renaming|relabel|alias|surface_invariance|audit|reference_match|calibrat"
    r"|families_present|modes_present|worlds_each",
    re.I,
)


def collect_gates(scratch: str) -> dict[str, dict[str, str]]:
    """version -> {gate id: описание}."""
    out: dict[str, dict[str, str]] = {}
    for path in sorted(glob.glob(scratch + "/**/results/verdict.json", recursive=True)):
        m = re.search(r"experiment[s]?_v0(\d+)", path)
        if not m:
            continue
        version = m.group(1)
        data = json.load(open(path))
        gates = data.get("scientific_gates")
        if not isinstance(gates, dict) or not gates:
            continue
        fallback: dict[str, str] = {}
        report = os.path.join(os.path.dirname(path), "REPORT.md")
        if os.path.exists(report):
            for line in open(report):
                hit = re.search(r"\b(S\d+)\b[^A-Za-z0-9]{1,6}(.{10,140})", line)
                if hit:
                    fallback.setdefault(hit.group(1), hit.group(2).strip())
        entry: dict[str, str] = {}
        for key in gates:
            hit = re.match(r"(S\d+)(?:_(.*))?$", key)
            if not hit:
                continue
            entry[hit.group(1)] = hit.group(2) or fallback.get(hit.group(1), "")
        out[version] = entry
    return out


def collect_covered(formal_dir: str) -> set[tuple[str, str]]:
    """Пары (версия, гейт), на которые в документах есть явная привязка."""
    covered: set[tuple[str, str]] = set()

    def scan(text: str) -> None:
        current = None
        for seg in re.split(r"(v0\.?(?:\d+))", text):
            head = re.fullmatch(r"v0\.?(\d+)", seg)
            if head:
                current = head.group(1)
                continue
            if current is None:
                continue
            for lo, hi in re.findall(r"S(\d+)\s*[-–]\s*S(\d+)", seg):
                for k in range(int(lo), int(hi) + 1):
                    covered.add((current, f"S{k}"))
            rest = re.sub(r"S(\d+)\s*[-–]\s*S(\d+)", "", seg)
            for g in re.findall(r"S(\d+)", rest):
                covered.add((current, f"S{g}"))

    cert = json.load(open(os.path.join(formal_dir, "final_certificate.json")))
    for entry in cert["theorems"].values():
        scan(entry.get("source", ""))
        scan(entry.get("downgrade", ""))
    for item in cert["not_formalized_by_design"]:
        scan(item)
    # PRD_BACKLOG.md перечисляет НЕпокрытые гейты — он не источник привязок.
    docs = [
        d
        for d in glob.glob(os.path.join(formal_dir, "PRD*.md"))
        if os.path.basename(d) != "PRD_BACKLOG.md"
    ]
    docs += [os.path.join(formal_dir, name) for name in ("ProofAudit.md", "README.md")]
    for doc in docs:
        if os.path.exists(doc):
            for line in open(doc):
                scan(line)
    return covered


def main() -> int:
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    scratch = sys.argv[1]
    verbose = "--list" in sys.argv
    formal_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    gates = collect_gates(scratch)
    covered = collect_covered(formal_dir)

    buckets: dict[str, dict[str, list[tuple[str, str]]]] = {
        "FORMALIZE": {},
        "NUM": {},
        "DECL": {},
        "INST": {},
        "UNLABELED": {},
    }
    total = hit = 0
    for version in sorted(gates, key=int):
        for gid, suffix in sorted(gates[version].items(), key=lambda kv: int(kv[0][1:])):
            total += 1
            if (version, gid) in covered:
                hit += 1
                continue
            if not suffix:
                cls = "UNLABELED"
            elif NUM.search(suffix):
                cls = "NUM"
            elif DECL.search(suffix):
                cls = "DECL"
            elif INST.search(suffix):
                cls = "INST"
            else:
                cls = "FORMALIZE"
            buckets[cls].setdefault(version, []).append((gid, suffix))

    print(f"научных гейтов всего: {total}")
    print(f"с явной привязкой:    {hit}")
    for cls in ("FORMALIZE", "NUM", "DECL", "INST", "UNLABELED"):
        count = sum(len(v) for v in buckets[cls].values())
        print(f"  {cls:<10} {count}")

    if verbose:
        for version in sorted(buckets["FORMALIZE"], key=int):
            items = buckets["FORMALIZE"][version]
            print(f"\nv0.{version} ({len(items)}):")
            for gid, suffix in items:
                print(f"  {gid}: {suffix}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
