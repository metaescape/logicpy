# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in Propositional Logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(
    antecedent_proof: Proof, consequent: Formula, conditional: InferenceRule
) -> Proof:
    """Converts the given proof of a formula `antecedent` to a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule(
        [], Formula("->", antecedent_proof.statement.conclusion, consequent)
    ).is_specialization_of(conditional)
    # Task 5.3a
    rules = antecedent_proof.rules | set([MP, conditional])
    assumptions = antecedent_proof.statement.assumptions
    statement = InferenceRule(assumptions, consequent)
    lines = list(antecedent_proof.lines)
    formula = Formula("->", antecedent_proof.statement.conclusion, consequent)
    lines.append(Proof.Line(formula, conditional, []))
    lines.append(Proof.Line(consequent, MP, [len(lines) - 2, len(lines) - 1]))
    return Proof(statement, rules, lines)


def combine_proofs(
    antecedent1_proof: Proof,
    antecedent2_proof: Proof,
    consequent: Formula,
    double_conditional: InferenceRule,
) -> Proof:
    """Combines the given proofs of two formulas `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `double_conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert (
        antecedent1_proof.statement.assumptions
        == antecedent2_proof.statement.assumptions
    )
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [],
        Formula(
            "->",
            antecedent1_proof.statement.conclusion,
            Formula("->", antecedent2_proof.statement.conclusion, consequent),
        ),
    ).is_specialization_of(double_conditional)
    # Task 5.3b

    tmp_consequent = Formula(
        "->", antecedent2_proof.statement.conclusion, consequent
    )

    tmp_proof = prove_corollary(
        antecedent1_proof, tmp_consequent, double_conditional
    )

    assumptions = tmp_proof.statement.assumptions
    statement = InferenceRule(assumptions, consequent)
    lines = list(tmp_proof.lines)
    offset = len(lines)
    for line in antecedent2_proof.lines:
        if hasattr(line, "assumptions"):
            a = [i + offset for i in line.assumptions]
            lines.append(Proof.Line(line.formula, line.rule, a))
        else:
            lines.append(line)

    lines.append(Proof.Line(consequent, MP, [len(lines) - 1, offset - 1]))
    return Proof(statement, tmp_proof.rules, lines)


def remove_assumption(proof: Proof) -> Proof:
    """Converts the given proof of some `conclusion` formula, the last
    assumption of which is an assumption `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    lines = []
    start = proof.statement.assumptions[-1]

    rules = proof.rules | set([MP, I0, I1, D])
    assumptions = proof.statement.assumptions[:-1]
    line_num = 0
    old2new = {}
    for i, line in enumerate(proof.lines):
        new_formula = Formula("->", start, line.formula)
        if line.formula == start:
            lines.append(Proof.Line(new_formula, rule=I0, assumptions=[]))
            line_num += 1
        elif line.rule == MP:
            j, k = [old2new[x] for x in line.assumptions]
            pq, pqr = lines[j].formula, lines[k].formula
            pqpr = Formula("->", pq, new_formula)
            d_spec = Formula("->", pqr, pqpr)
            lines.append(Proof.Line(d_spec, rule=D, assumptions=[]))  # 0
            lines.append(
                Proof.Line(pqpr, rule=MP, assumptions=[k, line_num])
            )  # 1
            lines.append(
                Proof.Line(new_formula, rule=MP, assumptions=[j, line_num + 1])
            )  # 2
            line_num += 3
        else:  # line.formula in assumptions/specialization of assumptions:
            lines.append(line)
            i1_spec = Formula("->", line.formula, new_formula)
            lines.append(Proof.Line(i1_spec, rule=I1, assumptions=[]))
            lines.append(
                Proof.Line(
                    new_formula, rule=MP, assumptions=[line_num, line_num + 1]
                )
            )
            line_num += 3

        old2new[i] = line_num - 1
    statement = InferenceRule(assumptions, lines[-1].formula)
    return Proof(statement, rules, lines)


def prove_from_opposites(
    proof_of_affirmation: Proof, proof_of_negation: Proof, conclusion: Formula
) -> Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.
        conclusion: formula to prove.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert (
        proof_of_affirmation.statement.assumptions
        == proof_of_negation.statement.assumptions
    )
    assert (
        Formula("~", proof_of_affirmation.statement.conclusion)
        == proof_of_negation.statement.conclusion
    )
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6
    return combine_proofs(
        proof_of_negation, proof_of_affirmation, conclusion, I2
    )


def prove_by_way_of_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, to a proof of `formula` from the
    same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Returns:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse("~(p->p)")
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == "~"
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
    f = proof.statement.assumptions[-1]  # ~formula
    proof = remove_assumption(proof)  # ~f->~(p->p)
    proof = prove_corollary(
        proof, Formula("->", Formula.parse("(p->p)"), f.first), N
    )

    n = len(proof.lines)
    lines = list(proof.lines)
    lines.append(Proof.Line(Formula.parse("(p->p)"), I0, []))
    lines.append(Proof.Line(f.first, MP, [n, n - 1]))
    statement = InferenceRule(proof.statement.assumptions, f.first)
    return Proof(statement, proof.rules, lines)
