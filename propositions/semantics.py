# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *

#: A model for propositional-logic formulas, a mapping from variable names to
#: truth values.
Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary is a model over some set of variable
    names.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variable
        names, ``False`` otherwise.
    """
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variable names over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variable names over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variable names of the
            given formula, to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.

    Examples:
        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': False})
        True

        >>> evaluate(Formula.parse('~(p&q76)'), {'p': True, 'q76': True})
        False
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    if formula.root == "T":
        return True
    if formula.root == "F":
        return False
    if is_unary(formula.root):
        return not evaluate(formula.first, model)
    if is_variable(formula.root):
        return model[formula.root]
    if formula.root == "&":
        return evaluate(formula.first, model) and evaluate(formula.second, model)
    if formula.root == "|":
        return evaluate(formula.first, model) or evaluate(formula.second, model)
    if formula.root == "+":
        return xor(evaluate(formula.first, model), evaluate(formula.second, model))
    if formula.root == "<->":
        return evaluate(formula.first, model) == evaluate(formula.second, model)
    if formula.root == "-&":
        return not (evaluate(formula.first, model) and evaluate(formula.second, model))
    if formula.root == "-|":
        return not (evaluate(formula.first, model) or evaluate(formula.second, model))
    if formula.root == "->":
        return not evaluate(formula.first, model) or evaluate(formula.second, model)

def xor(a, b):
    return (a or b) and (not a or not b)


def all_models(variables: Sequence[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variable names.

    Parameters:
        variables: variable names over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variable names. The
        order of the models is lexicographic according to the order of the given
        variable names, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]

        >>> list(all_models(['q', 'p']))
        [{'q': False, 'p': False}, {'q': False, 'p': True}, {'q': True, 'p': False}, {'q': True, 'p': True}]
    """
    n = len(variables)
    for v in variables:
        assert is_variable(v)

    # Task 2.2
    def bin2model(num):
        return {key: value == "1" for key, value in zip(variables, bin(num)[2:].zfill(n))}

    for i in range(2 ** n):
        yield bin2model(i)



def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    models.

    Parameters:
        formula: formula to calculate the truth value of.
        models: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.

    Examples:
        >>> list(truth_values(Formula.parse('~(p&q76)'), all_models(['p', 'q76'])))
        [True, True, True, False]
    """
    # Task 2.3
    for model in models:
        yield evaluate(formula, model)

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    vars = sorted(list(formula.variables())) 
    models = list(all_models(vars))
    vars = vars + [repr(formula)]
    length = [len(v) for v in vars]

    print("|", end="")
    for v in vars:
        print(f" {v} |", end="")
    print()

    print("|", end="")
    for v, n in zip(vars, length):
        print(f"-"*(n+2) + "|", end="")
    print()
    values = list(truth_values(formula, models))

    for model, res in zip(models, values):
        print("|", end="")
        for i, v in enumerate(sorted(model.keys())):
            value = "T" if model[v] else "F"
            print(f" {value.ljust(length[i] + 1, ' ')}|", end="")
        exp_value = "T" if res else "F"
        print(f" {exp_value.ljust(length[-1] + 1, ' ')}|")


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    return all(truth_values(formula, all_models(formula.variables())))

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    return not any(truth_values(formula, all_models(formula.variables())))

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    return not is_contradiction(formula)

def _synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single conjunctive
    clause that evaluates to ``True`` in the given model, and to ``False`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Task 2.6
    vars = list(model.keys())
    var = vars[0]
    base = Formula(var) if model[var] else Formula("~", Formula(var))

    for var in vars[1:]:
        f = Formula(var) if model[var] else Formula("~", Formula(var))
        base = Formula("&", f, base)

    return base



def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    p = variables[0]
    dnf = Formula("&", Formula(p), Formula("~" , Formula(p)))
    for model, value in zip(all_models(variables), values):
        cclause = _synthesize_for_model(model)
        if value:
            dnf = Formula("|", dnf, cclause)
    return dnf


def _synthesize_for_all_except_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single disjunctive
    clause that evaluates to ``False`` in the given model, and to ``True`` in
    any other model over the same variable names.

    Parameters:
        model: model over a nonempty set of variable names, in which the
            synthesized formula is to not hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    assert len(model.keys()) > 0
    # Optional Task 2.8
    vars = list(model.keys())
    var = vars[0]
    base = Formula(var)
    base = base if not model[var] else Formula("~", base)
    for var in vars[1:]:
        f = Formula(var)
        f = f if not model[var] else Formula("~", f)
        base = Formula("|", base, f)
    return base


def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in CNF over the given variable names,
    that has the specified truth table.

    Parameters:
        variables: nonempty set of variable names for the synthesized formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variable names, in the order returned
            by `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize_cnf(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Optional Task 2.9
    p = Formula(variables[0])
    f = Formula("|", p, Formula("~", p))
    for model, value in zip(all_models(variables), values):
        if not value:
            dclause = _synthesize_for_all_except_model(model)
            f = Formula("&", f, dclause)
    return f


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.

    Examples:
        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': True, 'q': False})
        False

        >>> evaluate_inference(InferenceRule([Formula('p')], Formula('q')),
        ...                    {'p': False, 'q': False})
        True
    """
    assert is_model(model)
    # Task 4.2
    for formula in rule.assumptions:
        if not evaluate(formula, model):
            return True
    return evaluate(rule.conclusion, model)
    

def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
    for model in all_models(rule.variables()):
        if not evaluate_inference(rule, model):
            return False
    return True
