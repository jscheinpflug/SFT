#!/usr/bin/env python3

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
NOTES_DIR = ROOT / "notes"
LEVEL1_DIR = NOTES_DIR / "level1_primary_comparison"
REFERENCE = ROOT / "references" / "1102.1209" / "1102.1209.tex"
EXISTING_NOTE = ROOT / "notes" / "konishi_linearized_ansatz" / "konishi_linearized_ansatz.tex"
FLAT_TABLE_TEX = LEVEL1_DIR / "generated_flat_space_irreps.tex"
KONISHI_TABLE_TEX = LEVEL1_DIR / "generated_konishi_irreps.tex"


def frac_from_tex(text: str) -> Fraction:
    text = text.strip()
    frac_match = re.fullmatch(r"\\frac\{(-?\d+)\}\{(\d+)\}", text)
    if frac_match:
        return Fraction(int(frac_match.group(1)), int(frac_match.group(2)))
    if "/" in text:
        n, d = text.split("/")
        return Fraction(int(n), int(d))
    return Fraction(int(text), 1)


def spin_to_key(spin: tuple[Fraction, Fraction]) -> tuple[int, int]:
    return (int(2 * spin[0]), int(2 * spin[1]))


def key_to_spin(key: tuple[int, int]) -> tuple[Fraction, Fraction]:
    return (Fraction(key[0], 2), Fraction(key[1], 2))


def format_half_integer(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def format_spin(key: tuple[int, int]) -> str:
    left, right = key_to_spin(key)
    return f"({format_half_integer(left)},{format_half_integer(right)})"


def format_so5(rep: tuple[int, int]) -> str:
    return f"<{rep[0]},{rep[1]}>"


def format_spin_tex(key: tuple[int, int]) -> str:
    left, right = key_to_spin(key)
    return rf"$({format_half_integer(left)},{format_half_integer(right)})$"


def format_so5_tex(rep: tuple[int, int]) -> str:
    return rf"$\langle {rep[0]},{rep[1]}\rangle$"


def format_delta_tex(delta: Fraction) -> str:
    if delta.denominator == 1:
        return rf"${delta.numerator}$"
    return rf"$\frac{{{delta.numerator}}}{{{delta.denominator}}}$"


def b2_dim(rep: tuple[int, int]) -> int:
    a, b = rep
    return ((a + 1) * (b + 1) * (a + b + 2) * (a + 2 * b + 3)) // 6


def so4_dim(spin: tuple[int, int]) -> int:
    return (spin[0] + 1) * (spin[1] + 1)


def so6_dim(rep: tuple[int, int, int]) -> int:
    a, b, c = rep
    return (
        (a + 1)
        * (b + 1)
        * (c + 1)
        * (a + b + 2)
        * (b + c + 2)
        * (a + b + c + 3)
        // 12
    )


def so6_to_d3_scaled(rep: tuple[int, int, int]) -> tuple[int, int, int]:
    a, b, c = rep
    return (a + c + 2 * b, a + c, c - a)


def d3_branch_to_b2(rep: tuple[int, int, int]) -> list[tuple[int, int]]:
    l1, l2, l3 = so6_to_d3_scaled(rep)
    branches = []
    for m1 in range(l2, l1 + 1, 2):
        for m2 in range(abs(l3), l2 + 1, 2):
            a = m2
            b = (m1 - m2) // 2
            branches.append((a, b))
    return sorted(branches, key=lambda item: (item[0] + 2 * item[1], item[0]))


POSITIVE_ROOTS_B2 = ((2, -2), (0, 2), (2, 0), (2, 2))
RHO_B2 = (3, 1)
SIMPLE_ROOTS_B2 = ((2, -2), (0, 2))


def b2_to_scaled(rep: tuple[int, int]) -> tuple[int, int]:
    a, b = rep
    return (a + 2 * b, a)


def scaled_to_b2(weight: tuple[int, int]) -> tuple[int, int]:
    u, v = weight
    return (v, (u - v) // 2)


WEYL_B2 = []
for permutation in ((0, 1), (1, 0)):
    perm_sign = 1 if permutation == (0, 1) else -1
    for sign_u in (-1, 1):
        for sign_v in (-1, 1):
            if permutation == (0, 1):
                matrix = ((sign_u, 0), (0, sign_v))
            else:
                matrix = ((0, sign_u), (sign_v, 0))
            determinant = perm_sign * sign_u * sign_v
            WEYL_B2.append((matrix[0], matrix[1], determinant))


def apply_weyl_b2(weight: tuple[int, int], element: tuple[tuple[int, int], tuple[int, int], int]) -> tuple[int, int]:
    (a, b), (c, d), _ = element
    u, v = weight
    return (a * u + b * v, c * u + d * v)


def dominant_b2(weight: tuple[int, int]) -> tuple[int, int]:
    u, v = abs(weight[0]), abs(weight[1])
    if u < v:
        u, v = v, u
    return (u, v)


def dot_scaled(left: tuple[int, int], right: tuple[int, int]) -> int:
    return left[0] * right[0] + left[1] * right[1]


@lru_cache(maxsize=None)
def b2_weight_multiplicities(rep: tuple[int, int]) -> dict[tuple[int, int], int]:
    highest = b2_to_scaled(rep)
    candidate_heights: dict[tuple[int, int], int] = {highest: 0}
    max_steps = highest[0] + highest[1] + 4
    for n1 in range(max_steps + 1):
        for n2 in range(max_steps + 1):
            mu = (
                highest[0] - n1 * SIMPLE_ROOTS_B2[0][0] - n2 * SIMPLE_ROOTS_B2[1][0],
                highest[1] - n1 * SIMPLE_ROOTS_B2[0][1] - n2 * SIMPLE_ROOTS_B2[1][1],
            )
            candidate_heights.setdefault(mu, n1 + n2)

    ordered_candidates = sorted(candidate_heights.items(), key=lambda item: (item[1], -item[0][0], -item[0][1]))
    multiplicities: dict[tuple[int, int], int] = {highest: 1}
    highest_shifted = (highest[0] + RHO_B2[0], highest[1] + RHO_B2[1])
    highest_norm = dot_scaled(highest_shifted, highest_shifted)

    for mu, _ in ordered_candidates[1:]:
        shifted_mu = (mu[0] + RHO_B2[0], mu[1] + RHO_B2[1])
        denominator = highest_norm - dot_scaled(shifted_mu, shifted_mu)
        if denominator <= 0:
            continue
        numerator = 0
        for root in POSITIVE_ROOTS_B2:
            k = 1
            while True:
                nu = (mu[0] + k * root[0], mu[1] + k * root[1])
                if nu not in multiplicities:
                    break
                numerator += 2 * dot_scaled(nu, root) * multiplicities[nu]
                k += 1
        if numerator:
            if numerator % denominator != 0:
                raise ValueError(f"Non-integral Freudenthal step for {rep} at weight {mu}: {numerator}/{denominator}")
            multiplicity = numerator // denominator
            if multiplicity > 0:
                multiplicities[mu] = multiplicity

    if sum(multiplicities.values()) != b2_dim(rep):
        raise ValueError(f"B2 character dimension mismatch for {rep}: {sum(multiplicities.values())} != {b2_dim(rep)}")
    return multiplicities


def tensor_product_b2(left: tuple[int, int], right: tuple[int, int]) -> Counter[tuple[int, int]]:
    product_weights: Counter[tuple[int, int]] = Counter()
    for weight_left, mult_left in b2_weight_multiplicities(left).items():
        for weight_right, mult_right in b2_weight_multiplicities(right).items():
            product_weights[(weight_left[0] + weight_right[0], weight_left[1] + weight_right[1])] += mult_left * mult_right

    remainder = Counter(product_weights)
    decomposition: Counter[tuple[int, int]] = Counter()
    while True:
        dominant_weights = [dominant_b2(weight) for weight, mult in remainder.items() if mult > 0]
        if not dominant_weights:
            break
        highest = max(set(dominant_weights), key=lambda item: (item[0], item[1]))
        multiplicity = remainder[highest]
        if multiplicity <= 0:
            raise ValueError(f"Non-positive highest multiplicity in B2 tensor product: {left} x {right}")
        decomposition[scaled_to_b2(highest)] += multiplicity
        character = b2_weight_multiplicities(scaled_to_b2(highest))
        for weight, mult in character.items():
            remainder[weight] -= multiplicity * mult
            if remainder[weight] == 0:
                del remainder[weight]
            elif remainder[weight] < 0:
                raise ValueError(f"Negative remainder in B2 tensor product: {left} x {right}")
    return decomposition


def tensor_product_so4(left: tuple[int, int], right: tuple[int, int]) -> Counter[tuple[int, int]]:
    result: Counter[tuple[int, int]] = Counter()
    for j_left in range(abs(left[0] - right[0]), left[0] + right[0] + 1, 2):
        for j_right in range(abs(left[1] - right[1]), left[1] + right[1] + 1, 2):
            result[(j_left, j_right)] += 1
    return result


LEFT_NS_COMPONENTS = [
    ((0, 0), (0, 0), 1, "44"),
    ((2, 2), (0, 0), 1, "44"),
    ((1, 1), (0, 1), 1, "44"),
    ((0, 0), (0, 2), 1, "44"),
    ((1, 1), (0, 0), 1, "84"),
    ((2, 0), (0, 1), 1, "84"),
    ((0, 2), (0, 1), 1, "84"),
    ((1, 1), (2, 0), 1, "84"),
    ((0, 0), (2, 0), 1, "84"),
]


LEFT_R_COMPONENTS = [
    ((2, 1), (1, 0), 1, "128"),
    ((1, 2), (1, 0), 1, "128"),
    ((0, 1), (1, 0), 1, "128"),
    ((1, 0), (1, 0), 1, "128"),
    ((1, 0), (1, 1), 1, "128"),
    ((0, 1), (1, 1), 1, "128"),
]


def build_flat_multiset() -> tuple[Counter[tuple[tuple[int, int], tuple[int, int]]], dict[str, Counter[tuple[tuple[int, int], tuple[int, int]]]]]:
    total: Counter[tuple[tuple[int, int], tuple[int, int]]] = Counter()
    by_sector: dict[str, Counter[tuple[tuple[int, int], tuple[int, int]]]] = {
        "NSNS": Counter(),
        "RR": Counter(),
        "NSR": Counter(),
        "RNS": Counter(),
    }

    sector_inputs = {
        "NSNS": (LEFT_NS_COMPONENTS, LEFT_NS_COMPONENTS),
        "RR": (LEFT_R_COMPONENTS, LEFT_R_COMPONENTS),
        "NSR": (LEFT_NS_COMPONENTS, LEFT_R_COMPONENTS),
        "RNS": (LEFT_R_COMPONENTS, LEFT_NS_COMPONENTS),
    }
    for sector, (left_components, right_components) in sector_inputs.items():
        for spin_left, sphere_left, mult_left, _ in left_components:
            for spin_right, sphere_right, mult_right, _ in right_components:
                so4_parts = tensor_product_so4(spin_left, spin_right)
                so5_parts = tensor_product_b2(sphere_left, sphere_right)
                factor = mult_left * mult_right
                for spin, so4_mult in so4_parts.items():
                    for sphere, so5_mult in so5_parts.items():
                        amount = factor * so4_mult * so5_mult
                        key = (spin, sphere)
                        total[key] += amount
                        by_sector[sector][key] += amount
    return total, by_sector


@dataclass(frozen=True)
class KonishiPrimary:
    delta: Fraction
    su4: tuple[int, int, int]
    spin: tuple[int, int]
    multiplicity: int


def parse_delta(label: str) -> Fraction:
    clean = label.replace(" ", "")
    clean = clean.replace(r"\dDelta", "2")
    if clean == "2":
        return Fraction(2, 1)
    if clean.startswith("2+"):
        rest = clean[2:]
        if rest.startswith(r"\frac"):
            nums = re.findall(r"\d+", rest)
            return Fraction(2, 1) + Fraction(int(nums[0]), int(nums[1]))
        return Fraction(2 + int(rest), 1)
    raise ValueError(f"Unrecognized delta label: {label}")


def extract_state_terms(expression: str) -> list[str]:
    terms = []
    i = 0
    while i < len(expression):
        if expression[i] != "[":
            i += 1
            continue
        start = i
        while expression[i] != "{":
            i += 1
        depth = 1
        i += 1
        while depth > 0:
            if expression[i] == "{":
                depth += 1
            elif expression[i] == "}":
                depth -= 1
            i += 1
        terms.append(expression[start:i])
    return terms


def parse_spin_multiplicities(content: str) -> list[tuple[int, tuple[int, int]]]:
    clean = content.replace(" ", "")
    clean = clean.replace(r"\frac{1}{2}", "1/2")
    pattern = re.compile(r"(?:(\d+))?\(([^,]+),([^)]+)\)")
    pieces = []
    for match in pattern.finditer(clean):
        multiplicity = int(match.group(1) or "1")
        left = frac_from_tex(match.group(2))
        right = frac_from_tex(match.group(3))
        pieces.append((multiplicity, spin_to_key((left, right))))
    return pieces


def parse_konishi_table() -> list[KonishiPrimary]:
    text = REFERENCE.read_text()
    start = text.index(r"\begin{tabular}")
    end = text.index(r"\caption{Long Konishi multiplet")
    block = text[start:end]
    block = block.split(r"\hline\hline", 1)[1]
    pattern = re.compile(r"\$\s*(.*?)\s*\$&\s*\$(.*?)\$\s*\\\\\s*\\hline", re.DOTALL)
    entries: list[KonishiPrimary] = []
    for delta_label, body in pattern.findall(block):
        delta = parse_delta(delta_label)
        compact = body.replace("\n", " ")
        terms = extract_state_terms(compact)
        for term in terms:
            match = re.match(r"\[(\d+),(\d+),(\d+)\]_\{(.*)\}", term)
            if not match:
                raise ValueError(f"Could not parse Table 1 term: {term}")
            su4 = tuple(int(match.group(i)) for i in range(1, 4))
            spins = parse_spin_multiplicities(match.group(4))
            for multiplicity, spin in spins:
                entries.append(KonishiPrimary(delta=delta, su4=su4, spin=spin, multiplicity=multiplicity))
    return entries


def build_konishi_multiset(entries: list[KonishiPrimary]) -> tuple[Counter[tuple[tuple[int, int], tuple[int, int]]], dict[tuple[tuple[int, int], tuple[int, int]], Counter[Fraction]]]:
    total: Counter[tuple[tuple[int, int], tuple[int, int]]] = Counter()
    deltas: dict[tuple[tuple[int, int], tuple[int, int]], Counter[Fraction]] = defaultdict(Counter)
    for entry in entries:
        for sphere_rep in d3_branch_to_b2(entry.su4):
            key = (entry.spin, sphere_rep)
            total[key] += entry.multiplicity
            deltas[key][entry.delta] += entry.multiplicity
    return total, deltas


def compare_existing_note() -> dict[str, object]:
    text = EXISTING_NOTE.read_text()
    expected_branches = {}
    for match in re.finditer(r"\[([0-4]),([0-4]),([0-4])\]\s*&->\s*(.*?)\s*,", text):
        su4 = tuple(int(match.group(i)) for i in range(1, 4))
        rhs = match.group(4)
        reps = []
        for rep_match in re.finditer(r"\\langle\s*(\d+),(\d+)\s*\\rangle", rhs):
            reps.append((int(rep_match.group(1)), int(rep_match.group(2))))
        expected_branches[su4] = sorted(reps)

    actual_branches = {su4: d3_branch_to_b2(su4) for su4 in expected_branches}
    branch_mismatches = {
        su4: (expected_branches[su4], actual_branches[su4])
        for su4 in expected_branches
        if expected_branches[su4] != actual_branches[su4]
    }

    note_flat = {
        "44": Counter({
            ((0, 0), (0, 0)): 1,
            ((2, 2), (0, 0)): 1,
            ((1, 1), (0, 1)): 1,
            ((0, 0), (0, 2)): 1,
        }),
        "84": Counter({
            ((1, 1), (0, 0)): 1,
            ((2, 0), (0, 1)): 1,
            ((0, 2), (0, 1)): 1,
            ((1, 1), (2, 0)): 1,
            ((0, 0), (2, 0)): 1,
        }),
        "128": Counter({
            ((2, 1), (1, 0)): 1,
            ((1, 2), (1, 0)): 1,
            ((0, 1), (1, 0)): 1,
            ((1, 0), (1, 0)): 1,
            ((1, 0), (1, 1)): 1,
            ((0, 1), (1, 1)): 1,
        }),
    }
    actual_flat = {
        "44": Counter({(spin, rep): mult for spin, rep, mult, parent in LEFT_NS_COMPONENTS if parent == "44"}),
        "84": Counter({(spin, rep): mult for spin, rep, mult, parent in LEFT_NS_COMPONENTS if parent == "84"}),
        "128": Counter({(spin, rep): mult for spin, rep, mult, parent in LEFT_R_COMPONENTS}),
    }
    flat_mismatches = {
        key: (note_flat[key], actual_flat[key])
        for key in note_flat
        if note_flat[key] != actual_flat[key]
    }
    return {
        "branch_mismatches": branch_mismatches,
        "flat_mismatches": flat_mismatches,
    }


def format_delta(delta: Fraction) -> str:
    return format_half_integer(delta)


def render_counter(counter: Counter[tuple[tuple[int, int], tuple[int, int]]], deltas: dict[tuple[tuple[int, int], tuple[int, int]], Counter[Fraction]] | None = None) -> str:
    lines = []
    for (spin, sphere), multiplicity in sorted(counter.items(), key=lambda item: (item[0][0], item[0][1][0] + 2 * item[0][1][1], item[0][1])):
        line = f"{format_spin(spin)} x {format_so5(sphere)} : {multiplicity}"
        if deltas is not None:
            delta_text = ", ".join(
                f"Delta={format_delta(delta)} -> {count}"
                for delta, count in sorted(deltas[(spin, sphere)].items(), key=lambda item: item[0])
            )
            line += f" [{delta_text}]"
        lines.append(line)
    return "\n".join(lines)


def build_report() -> str:
    konishi_entries = parse_konishi_table()
    flat_total, flat_by_sector = build_flat_multiset()
    konishi_total, konishi_deltas = build_konishi_multiset(konishi_entries)

    matched = Counter()
    flat_only = Counter()
    konishi_only = Counter()
    for key in set(flat_total) | set(konishi_total):
        common = min(flat_total[key], konishi_total[key])
        if common:
            matched[key] = common
        if flat_total[key] > common:
            flat_only[key] = flat_total[key] - common
        if konishi_total[key] > common:
            konishi_only[key] = konishi_total[key] - common

    note_check = compare_existing_note()

    lines = []
    lines.append("Independent branching scan for mass-level-1 primaries")
    lines.append("")
    lines.append("SO(6) -> SO(5) branchings derived independently:")
    all_su4 = sorted({entry.su4 for entry in konishi_entries})
    for su4 in all_su4:
        branches = ", ".join(format_so5(rep) for rep in d3_branch_to_b2(su4))
        lines.append(f"[{su4[0]},{su4[1]},{su4[2]}] -> {branches}")
    lines.append("")
    lines.append("Independent first-massive flat-space decompositions:")
    for label, components in (
        ("44", Counter({(spin, rep): mult for spin, rep, mult, parent in LEFT_NS_COMPONENTS if parent == "44"})),
        ("84", Counter({(spin, rep): mult for spin, rep, mult, parent in LEFT_NS_COMPONENTS if parent == "84"})),
        ("128", Counter({(spin, rep): mult for spin, rep, mult, parent in LEFT_R_COMPONENTS})),
    ):
        lines.append(f"{label}:")
        for (spin, sphere), multiplicity in sorted(components.items()):
            lines.append(f"  {format_spin(spin)} x {format_so5(sphere)} : {multiplicity}")
    lines.append("")
    lines.append(f"Flat-space total irrep multiplicity count: {sum(flat_total.values())}")
    lines.append(f"Konishi total irrep multiplicity count after SO(6) branching: {sum(konishi_total.values())}")
    lines.append("")
    lines.append("Sector totals:")
    for sector, counter in flat_by_sector.items():
        lines.append(f"  {sector}: {sum(counter.values())}")
    lines.append("")
    lines.append("Matched irreps:")
    lines.append(render_counter(matched, konishi_deltas))
    lines.append("")
    lines.append("Flat-space irreps not fully realized in Konishi:")
    lines.append(render_counter(flat_only))
    lines.append("")
    lines.append("Konishi irreps not fully realized by flat-space level-1:")
    lines.append(render_counter(konishi_only, konishi_deltas))
    lines.append("")
    lines.append("Comparison to existing notes:")
    lines.append(f"  SO(6) -> SO(5) branching mismatches: {len(note_check['branch_mismatches'])}")
    lines.append(f"  Flat 44/84/128 decomposition mismatches: {len(note_check['flat_mismatches'])}")
    return "\n".join(lines)


def sorted_irrep_items(counter: Counter[tuple[tuple[int, int], tuple[int, int]]]):
    return sorted(
        counter.items(),
        key=lambda item: (item[0][0][0], item[0][0][1], item[0][1][0] + 2 * item[0][1][1], item[0][1][0], item[0][1][1]),
    )


def write_flat_table_tex(flat_total: Counter[tuple[tuple[int, int], tuple[int, int]]], flat_by_sector: dict[str, Counter[tuple[tuple[int, int], tuple[int, int]]]]) -> None:
    lines = []
    lines.append(r"\begin{longtable}{c c c c c c}")
    lines.append(r"\caption{Complete flat-space primary-state irreps after reducing the first-massive spectrum, grouped by compact spin label.}\label{tab:flat-full}\\")
    lines.append(r"\toprule")
    lines.append(r"$(s_L,s_R)$ & $\SO(5)$ irrep & total & NSNS & RR & mixed \\")
    lines.append(r"\midrule")
    lines.append(r"\endfirsthead")
    lines.append(r"\toprule")
    lines.append(r"$(s_L,s_R)$ & $\SO(5)$ irrep & total & NSNS & RR & mixed \\")
    lines.append(r"\midrule")
    lines.append(r"\endhead")
    current_spin = None
    for (spin, sphere), total in sorted_irrep_items(flat_total):
        if spin != current_spin:
            if current_spin is not None:
                lines.append(r"\midrule")
            lines.append(rf"\multicolumn{{6}}{{l}}{{\textbf{{Spin {format_spin_tex(spin)}}}}}\\")
            current_spin = spin
        nsns = flat_by_sector["NSNS"][(spin, sphere)]
        rr = flat_by_sector["RR"][(spin, sphere)]
        mixed = flat_by_sector["NSR"][(spin, sphere)] + flat_by_sector["RNS"][(spin, sphere)]
        lines.append(
            rf"{format_spin_tex(spin)} & {format_so5_tex(sphere)} & {total} & {nsns} & {rr} & {mixed} \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{longtable}")
    FLAT_TABLE_TEX.write_text("\n".join(lines) + "\n")


def write_konishi_table_tex(konishi_total: Counter[tuple[tuple[int, int], tuple[int, int]]], konishi_deltas: dict[tuple[tuple[int, int], tuple[int, int]], Counter[Fraction]]) -> None:
    lines = []
    lines.append(r"\begin{longtable}{c c c p{8.8cm}}")
    lines.append(r"\caption{Complete Konishi primary-state irreps after branching $\SO(6)\to \SO(5)$, organized by compact spin label and graded by $\Delta_0$.}\label{tab:konishi-full}\\")
    lines.append(r"\toprule")
    lines.append(r"$(s_L,s_R)$ & $\SO(5)$ irrep & total & $\Delta_0$ grading \\")
    lines.append(r"\midrule")
    lines.append(r"\endfirsthead")
    lines.append(r"\toprule")
    lines.append(r"$(s_L,s_R)$ & $\SO(5)$ irrep & total & $\Delta_0$ grading \\")
    lines.append(r"\midrule")
    lines.append(r"\endhead")
    current_spin = None
    for (spin, sphere), total in sorted_irrep_items(konishi_total):
        if spin != current_spin:
            if current_spin is not None:
                lines.append(r"\midrule")
            lines.append(rf"\multicolumn{{4}}{{l}}{{\textbf{{Spin {format_spin_tex(spin)}}}}}\\")
            current_spin = spin
        grading = ", ".join(
            rf"{format_delta_tex(delta)}: {count}"
            for delta, count in sorted(konishi_deltas[(spin, sphere)].items(), key=lambda item: item[0])
        )
        lines.append(
            rf"{format_spin_tex(spin)} & {format_so5_tex(sphere)} & {total} & {grading} \\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{longtable}")
    KONISHI_TABLE_TEX.write_text("\n".join(lines) + "\n")


def write_tex_tables() -> None:
    flat_total, flat_by_sector = build_flat_multiset()
    konishi_total, konishi_deltas = build_konishi_multiset(parse_konishi_table())
    write_flat_table_tex(flat_total, flat_by_sector)
    write_konishi_table_tex(konishi_total, konishi_deltas)


def main() -> None:
    write_tex_tables()
    report = build_report()
    print(report)


if __name__ == "__main__":
    main()
