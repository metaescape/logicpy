# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/completeness.py

"""Building blocks for proving the Completeness Theorem for Predicate Logic."""

from typing import AbstractSet, Container, Set, Union

from logic_utils import fresh_constant_name_generator

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import *


def get_constants(formulas: AbstractSet[Formula]) -> Set[str]:
    """Finds all constant names in the given formulas.

    Parameters:
        formulas: formulas to find all constant names in.

    Returns:
        A set of all constant names used in one or more of the given formulas.
    """
    constants = set()
    for formula in formulas:
        constants.update(formula.constants())
    return constants


def is_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if the given set of sentences is primitively, universally, and
        existentially closed; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    return (
        is_primitively_closed(sentences)
        and is_universally_closed(sentences)
        and is_existentially_closed(sentences)
    )


def is_primitively_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    primitively closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every n-ary relation name from the given sentences, and
        for every n (not necessarily distinct) constant names from the given
        sentences, either the invocation of this relation name over these
        constant names (in order), or the negation of this invocation (or both),
        is one of the given sentences; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.1a
    from itertools import product

    constants = get_constants(sentences)
    relations = set()
    for sentence in sentences:
        for relation, arities in sentence.relations():
            relations.add((relation, arities))
    for relation, arities in relations:
        for args in product(constants, repeat=arities):

            if (
                Formula(relation, [Term(a) for a in args]) not in sentences
                and Formula("~", Formula(relation, [Term(a) for a in args]))
                not in sentences
            ):
                return False

    return True


def is_universally_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    universally closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every universally quantified sentence from the given set
        of sentences, and for every constant name from these sentences, the
        statement quantified by this sentence, with every free occurrence of the
        universal quantification variable name replaced with this constant name,
        is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.1b
    constants = get_constants(sentences)
    for sentence in sentences:
        if sentence.root == "A":
            for constant in constants:
                if (
                    sentence.statement.substitute(
                        {sentence.variable: Term(constant)}
                    )
                    not in sentences
                ):
                    return False
    return True


def is_existentially_closed(sentences: AbstractSet[Formula]) -> bool:
    """Checks whether the given set of prenex-normal-form sentences is
    existentially closed.

    Parameters:
        sentences: set of prenex-normal-form sentences to check.

    Returns:
        ``True`` if for every existentially quantified sentence from the given
        set of sentences there exists a constant name such that the statement
        quantified by this sentence, with every free occurrence of the
        existential quantification variable name replaced with this constant
        name, is also in the given set; ``False`` otherwise.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.1c
    constants = get_constants(sentences)
    for sentence in sentences:
        if sentence.root == "E":
            found = False
            for constant in constants:
                if (
                    sentence.statement.substitute(
                        {sentence.variable: Term(constant)}
                    )
                    in sentences
                ):
                    found = True
                    break
            if not found:
                return False
    return True


def find_unsatisfied_quantifier_free_sentence(
    sentences: Container[Formula], model: Model[str], unsatisfied: Formula
) -> Formula:
    """
    Given a universally and existentially closed set of prenex-normal-form
    sentences, given a model whose universe is the set of all constant names
    from the given sentences, and given a sentence from the given set that the
    given model does not satisfy, finds a quantifier-free sentence from the
    given set that the given model does not satisfy.

    Parameters:
        sentences: universally and existentially closed set of
            prenex-normal-form sentences, which is only to be accessed using
            containment queries, i.e., using the ``in`` operator as in:

            >>> if sentence in sentences:
            ...     print('contained!')

        model: model for all element names from the given sentences, whose
            universe is `get_constants`\ ``(``\ `sentences`\ ``)``.
        unsatisfied: sentence (which possibly contains quantifiers) from the
            given sentences that is not satisfied by the given model.

    Returns:
        A quantifier-free sentence from the given set of sentences that is not
        satisfied by the given model.
    """
    # We assume that every formula in sentences is in prenex normal form and has
    # no free variable names, that sentences is universally and existentially
    # closed, and that the set of constant names that appear somewhere in
    # sentences is model.universe; but we cannot assert these since we cannot
    # iterate over sentences.
    for constant in model.universe:
        assert is_constant(constant)
    assert is_in_prenex_normal_form(unsatisfied)
    assert len(unsatisfied.free_variables()) == 0
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2
    if is_quantifier_free(unsatisfied):
        return unsatisfied

    for constant in model.universe:
        sub_unsatisfied = unsatisfied.statement.substitute(
            {unsatisfied.variable: Term(constant)}
        )

        if model.evaluate_formula(sub_unsatisfied):
            continue
        if unsatisfied.root == "A" or (sub_unsatisfied in sentences):
            return find_unsatisfied_quantifier_free_sentence(
                sentences,
                model,
                sub_unsatisfied,
            )
    return unsatisfied


def get_primitives(quantifier_free: Formula) -> Set[Formula]:
    """Finds all primitive subformulas of the given quantifier-free formula.

    Parameters:
        quantifier_free: quantifier-free formula that contains no function names
            and no equalities, whose subformulas are to be searched.

    Returns:
        The primitive subformulas (i.e., relation invocations) of which the
        given quantifier-free formula is composed using logical operators.

    Examples:
        The primitive subformulas of ``'(R(c1,d)|~(Q(c1)->~R(c2,a)))'`` are
        ``'R(c1,d)'``, ``'Q(c1)'``, and ``'R(c2,a)'``.
    """
    assert is_quantifier_free(quantifier_free)
    assert len(quantifier_free.functions()) == 0
    assert "=" not in str(quantifier_free)
    # Task 12.3a
    if is_relation(quantifier_free.root):
        return {quantifier_free}
    if is_unary(quantifier_free.root):
        return get_primitives(quantifier_free.first)
    # if is_binary(quantifier_free.root):
    return get_primitives(quantifier_free.first) | get_primitives(
        quantifier_free.second
    )


def model_or_inconsistency(
    sentences: AbstractSet[Formula],
) -> Union[Model[str], Proof]:
    """Either finds a model in which the given closed set of prenex-normal-form
    sentences holds, or proves a contradiction from these sentences.

    Parameters:
        sentences: closed set of prenex-normal-form sentences that contain no
            function names and no equalities, to either find a model of, or
            prove a contradiction from.

    Returns:
        A model in which all of the given sentences hold if such exists,
        otherwise a valid proof of  a contradiction from the given formulas via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_closed(sentences)
    for sentence in sentences:
        assert len(sentence.functions()) == 0
        assert "=" not in str(sentence)
    # Task 12.3b

    constants = get_constants(sentences)

    relation_interpretations = {}
    for sentence in sentences:
        if is_relation(sentence.root):
            if sentence.root not in relation_interpretations:
                relation_interpretations[sentence.root] = set()
            relation_interpretations[sentence.root].add(
                tuple([term.root for term in sentence.arguments])
            )

    model = Model(
        universe=constants,
        constant_interpretations={k: k for k in constants},
        relation_interpretations=relation_interpretations,
    )
    if model.is_model_of(sentences):
        return model

    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            quantier_free = find_unsatisfied_quantifier_free_sentence(
                sentences, model, sentence
            )
            break

    assumptions = set({quantier_free})

    for sentence in sentences:
        if str(sentence) in str(quantier_free):
            assumptions.add(sentence)
        if is_unary(sentence.root) and str(sentence.first) in str(
            quantier_free
        ):
            assumptions.add(sentence)

    prover = Prover(assumptions)

    p = quantier_free

    idx_set = set()
    for assumption in assumptions:
        idx_set.add(prover.add_assumption(assumption))

    prover.add_tautological_implication(
        Formula("~", Formula("->", p, p)), idx_set
    )

    return prover.qed()


def combine_contradictions(
    proof_from_affirmation: Proof, proof_from_negation: Proof
) -> Proof:
    """Combines the given two proofs of contradictions, both from the same
    assumptions/axioms except that the latter has an extra assumption that is
    the negation of an extra assumption that the former has, into a single proof
    of a contradiction from only the common assumptions/axioms.

    Parameters:
        proof_from_affirmation: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        proof_from_negation: valid proof of a contradiction from the same
            assumptions/axioms of `proof_from_affirmation`, but with one
            simple assumption (i.e., without any templates) `assumption`
            replaced with its negation ``'~``\ `assumption`\ ``'``.

    Returns:
        A valid proof of a contradiction from only the assumptions/axioms common
        to the given proofs (i.e., without `assumption` or its negation).
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    common_assumptions = proof_from_affirmation.assumptions.intersection(
        proof_from_negation.assumptions
    )
    assert (
        len(common_assumptions) == len(proof_from_affirmation.assumptions) - 1
    )
    assert len(common_assumptions) == len(proof_from_negation.assumptions) - 1
    affirmed_assumption = list(
        proof_from_affirmation.assumptions - common_assumptions
    )[0]
    negated_assumption = list(
        proof_from_negation.assumptions - common_assumptions
    )[0]
    assert len(affirmed_assumption.templates) == 0
    assert len(negated_assumption.templates) == 0
    assert negated_assumption.formula == Formula(
        "~", affirmed_assumption.formula
    )
    assert proof_from_affirmation.assumptions.issuperset(Prover.AXIOMS)
    assert proof_from_negation.assumptions.issuperset(Prover.AXIOMS)
    for assumption in common_assumptions.union(
        {affirmed_assumption, negated_assumption}
    ):
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.4
    prover = Prover(common_assumptions)
    affirmed_proof = remove_assumption(
        proof_from_affirmation, affirmed_assumption.formula
    )
    negated_proof = remove_assumption(
        proof_from_negation, negated_assumption.formula
    )

    step1 = prover.add_proof(affirmed_proof.conclusion, affirmed_proof)
    step2 = prover.add_proof(negated_proof.conclusion, negated_proof)
    step3 = prover.add_tautological_implication(
        proof_from_affirmation.conclusion, {step1, step2}
    )

    return prover.qed()


def eliminate_universal_instantiation_assumption(
    proof: Proof, universal: Formula, constant: str
) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `universal` and `instantiation`, where the latter is the universal
    instantiation of the former with the constant name `constant`, to a proof
    of a contradiction from the same assumptions without `instantiation`.

    Parameters:
        proof: valid proof of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        universal: assumption of the given proof that is universally quantified.
        constant: constant name such that the formula `instantiation` obtained
            from the statement quantified by `universal` by replacing all free
            occurrences of the universal quantification variable name by the
            given constant name, is an assumption of the given proof.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `instantiation`.
    """
    assert proof.is_valid()
    assert Schema(universal) in proof.assumptions
    assert universal.root == "A"
    assert is_constant(constant)
    assert (
        Schema(
            universal.statement.substitute(
                {universal.variable: Term(constant)}
            )
        )
        in proof.assumptions
    )
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
    # Task 12.5

    instance = universal.statement.substitute(
        {universal.variable: Term(constant)}
    )
    # A(x)[P(x)]:  ~P(c)
    proof1 = prove_by_way_of_contradiction(proof, instance)
    prover = Prover(proof1.assumptions)
    step1 = prover.add_proof(proof1.conclusion, proof1)  # ~P(c)
    ui = Formula("->", universal, instance)
    step2 = prover.add_instantiated_assumption(
        ui,
        Prover.UI,
        {
            "R": instance.substitute({constant: Term("_")}),
            "c": constant,
            "x": universal.variable,
        },
    )  # Ax[P(x)] -> P(c)
    step3 = prover.add_assumption(universal)  # Ax[P(c)]
    step4 = prover.add_mp(instance, step3, step2)  # P(c)
    prover.add_tautological_implication(proof.conclusion, {step1, step4})
    return prover.qed()


def universal_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with all universal instantiations of each
    universally quantified sentence from these sentences, with respect to all
    constant names from these sentences.

    Parameters:
        sentences: prenex-normal-form sentences to augment with their universal
            instantiations.

    Returns:
        A set of all of the given sentences, and in addition any formula that
        can be obtained from the statement quantified by any universally
        quantified sentence from the given sentences by replacing all
        occurrences of the quantification variable name with some constant name
        from the given sentences.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.6
    constants = get_constants(sentences)
    new_sentences = set()
    for sentence in sentences:
        if sentence.root == "A":
            for constant in constants:
                new_sentences.add(
                    sentence.statement.substitute(
                        {sentence.variable: Term(constant)}
                    )
                )

    return sentences | new_sentences


def replace_constant(
    proof: Proof, constant: str, variable: str = "zz"
) -> Proof:
    """Replaces all occurrences of the given constant name in the given proof
    with the given variable name.

    Parameters:
        proof: valid proof in which to replace.
        constant: constant name that does not appear as a template constant name
            in any of the assumptions of the given proof.
        variable: variable name that does not appear anywhere in the given proof
            or in its assumptions.

    Returns:
        A valid proof where every occurrence of the given constant name in the
        given proof and in its assumptions is replaced with the given variable
        name.
    """
    assert proof.is_valid()
    assert is_constant(constant)
    assert is_variable(variable)
    for assumption in proof.assumptions:
        assert constant not in assumption.templates
        assert variable not in assumption.formula.variables()
    for line in proof.lines:
        assert variable not in line.formula.variables()
    # Task 12.7a

    new_assumptions = set()
    for ass in proof.assumptions:

        new_ass = Schema(
            ass.formula.substitute({constant: Term(variable)}),
            ass.templates,
        )
        new_assumptions.add(new_ass)

    prover = Prover(new_assumptions)

    for line in proof.lines:
        new_formula = line.formula.substitute({constant: Term(variable)})
        if isinstance(line, Proof.AssumptionLine):
            new_map = {}
            for k, v in line.instantiation_map.items():
                if not isinstance(v, str):
                    new_map[k] = v.substitute({constant: Term(variable)})
                else:
                    new_map[k] = v
            new_ass = Schema(
                line.assumption.formula.substitute({constant: Term(variable)}),
                line.assumption.templates,
            )
            new_line = Proof.AssumptionLine(new_formula, new_ass, new_map)

            prover._add_line(new_line)
        elif isinstance(line, Proof.MPLine):
            prover.add_mp(
                new_formula,
                line.antecedent_line_number,
                line.conditional_line_number,
            )
        elif isinstance(line, Proof.UGLine):
            prover.add_ug(new_formula, line.nonquantified_line_number)
        elif isinstance(line, Proof.TautologyLine):
            new_line = Proof.TautologyLine(new_formula)
            prover._add_line(new_line)

    return prover.qed()


def eliminate_existential_witness_assumption(
    proof: Proof, existential: Formula, constant: str
) -> Proof:
    """Converts the given proof of a contradiction, whose assumptions/axioms
    include `existential` and `witness`, where the latter is the existential
    witness of the former with the witnessing constant name `constant`, to a
    proof of a contradiction from the same assumptions without `witness`.

    Parameters:
        proof: valid proof, which does not contain the variable name ``'zz'`` in
            its lines or assumptions, of a contradiction from one or more
            assumptions/axioms that are all sentences and that include
            `~predicates.prover.Prover.AXIOMS`.
        existential: assumption of the given proof that is existentially
            quantified.
        constant: constant name such that the formula `witness` obtained from
            from the statement quantified by `existential` by replacing all free
            occurrences of the existential quantification variable name by the
            given constant name, is an assumption of the given proof, and such
            that this constant name does not appear in any assumption of the
            given proof except `witness`.

    Returns:
        A valid proof of a contradiction from the assumptions/axioms of the
        given proof except `witness`.
    """
    assert proof.is_valid()
    assert Schema(existential) in proof.assumptions
    assert existential.root == "E"
    assert is_constant(constant)
    witness = existential.statement.substitute(
        {existential.variable: Term(constant)}
    )
    assert Schema(witness) in proof.assumptions
    for assumption in proof.assumptions:
        assert len(assumption.formula.free_variables()) == 0
        assert "zz" not in assumption.formula.variables()
    for assumption in proof.assumptions - {Schema(witness)}:
        assert constant not in assumption.formula.constants()
    for line in proof.lines:
        assert "zz" not in line.formula.variables()
    # Task 12.7b

    proof_without_witness = replace_constant(proof, constant, "zz")

    zz_witness = witness.substitute({constant: Term("zz")})

    # proof of ~zz_witness from E(x)[P(x)]
    new_proof = prove_by_way_of_contradiction(
        proof_without_witness, zz_witness
    )
    prover = Prover(proof.assumptions - {Schema(witness)})

    step1 = prover.add_assumption(existential)
    neg_zz_witness = Formula("~", zz_witness)
    step2 = prover.add_proof(neg_zz_witness, new_proof)

    # A(x)[~P(zz)]
    # ~P(x)
    neg_instance = neg_zz_witness.substitute(
        {"zz": Term(existential.variable)}
    )
    neg_idx = prover.add_free_instantiation(
        neg_instance,
        step2,
        {"zz": existential.variable},
    )
    # p->p
    tautological1 = Formula("->", zz_witness, zz_witness)

    # P(x) -> ~(p->p)
    tautological2 = Formula(
        "->", neg_instance.first, Formula("~", tautological1)
    )  # zz_witness -> contradiction

    # p->p
    tat_idx = prover.add_tautology(tautological1)

    imply_idx = prover.add_tautological_implication(
        tautological2, {tat_idx, neg_idx}
    )
    # P(x)->~(p->p)&E(x)P(x) : ~(p->p)
    prover.add_existential_derivation(
        Formula("~", tautological1), step1, imply_idx
    )

    return prover.qed()


def existential_closure_step(sentences: AbstractSet[Formula]) -> Set[Formula]:
    """Augments the given sentences with an existential witness that uses a new
    constant name, for each existentially quantified sentence from these
    sentences for which an existential witness is missing.

    Parameters:
        sentences: prenex-normal-form sentences to augment with any missing
            existential witnesses.

    Returns:
        A set of all of the given sentences, and in addition for every
        existentially quantified sentence from the given sentences, a formula
        obtained from the statement quantified by that sentence by replacing all
        occurrences of the quantification variable name with a new constant name
        obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_constant_name_generator`\ ``)``.
    """
    for sentence in sentences:
        assert (
            is_in_prenex_normal_form(sentence)
            and len(sentence.free_variables()) == 0
        )
    # Task 12.8

    new_sentences = set()

    E_sentences = set(
        [sentence for sentence in sentences if sentence.root == "E"]
    )

    constants = get_constants(sentences)

    removed_E = set()
    for sentence in E_sentences:
        for constant in constants:
            witness = sentence.statement.substitute(
                {sentence.variable: Term(constant)}
            )
            if witness in sentences:
                removed_E.add(sentence)
                break

    for sentence in E_sentences:
        if sentence not in removed_E:
            constant = next(fresh_constant_name_generator)
            new_sentences.add(
                sentence.statement.substitute(
                    {sentence.variable: Term(constant)}
                )
            )

    return sentences | new_sentences
