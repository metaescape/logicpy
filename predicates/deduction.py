# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
import re


def remove_assumption(
    proof: Proof, assumption: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.
        print_as_proof_forms: flag specifying whether the proof of
            ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.1

    assumptions = {a for a in proof.assumptions if a != Schema(assumption)}
    prover = Prover(assumptions, print_as_proof_forms)

    line_map = {}

    for i, line in enumerate(proof.lines):
        p_original = Formula("->", assumption, line.formula)

        if isinstance(line, Proof.AssumptionLine):
            if line.formula == assumption:
                idx = prover.add_tautology(p_original)
            else:
                idx = prover._add_line(line)  # add original formula
                # add p->X and update line_map

                idx = prover.add_tautological_implication(p_original, {idx})
        elif isinstance(line, Proof.UGLine):
            statement = line.formula.statement
            v = str(line.formula.variable)

            if v in assumption.free_variables():
                new_variable = next(fresh_variable_name_generator)
                assumption = assumption.substitute({v: new_variable})

            p_original = Formula("->", assumption, statement)
            p_original = Formula("A", v, p_original)
            # add UG
            line_num = line_map[line.nonquantified_line_number]
            idx_ug = prover.add_ug(p_original, line_num)

            result = Formula("->", assumption, line.formula)

            us_formula = Formula("->", p_original, result)

            US = Schema(
                Formula.parse("(Ax[(Q()->R(x))]->(Q()->Ax[R(x)]))"),
                {"Q", "R", "x"},
            )
            Q = assumption
            R = statement.substitute({v: Term.parse("_")})

            idx = prover.add_instantiated_assumption(
                us_formula,
                Prover.US,
                {"Q": Q, "R": R, "x": line.formula.variable},
            )

            idx = prover.add_mp(result, idx_ug, idx)

        elif isinstance(line, Proof.MPLine):
            idx = prover.add_tautological_implication(
                p_original,
                {
                    line_map[line.antecedent_line_number],
                    line_map[line.conditional_line_number],
                },
            )
        else:  # tautological line
            idx = prover.add_tautology(p_original)

        line_map[i] = idx

    return prover.qed()


def prove_by_way_of_contradiction(proof: Proof, assumption: Formula) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable name that is free in this assumption.

    Returns:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    # Task 11.2
    new_proof = remove_assumption(proof, assumption)
    prover = Prover(new_proof.assumptions)
    idx = prover.add_proof(new_proof.conclusion, new_proof)
    prover.add_tautological_implication(
        f"~{assumption}",
        {idx},
    )
    return prover.qed()
