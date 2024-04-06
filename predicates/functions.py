# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/functions.py

"""Syntactic conversion of predicate-logic formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator, is_z_and_number

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function interpretations, replacing each function interpretation with a
    canonically corresponding relation interpretation.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            interpretations in this model.

    Returns:
        A model obtained from the given model by replacing every function
        interpretation of a function name with a relation interpretation of the
        canonically corresponding relation name, such that the relation
        interpretation contains any tuple
        ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1` is the
        output of the function interpretation for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_interpretations:
        assert (
            function_name_to_relation_name(function)
            not in model.relation_interpretations
        )
    # Task 8.1

    universe = model.universe
    constant_interpretations = model.constant_interpretations
    relation_interpretations = dict(model.relation_interpretations)

    function_interpretations = dict()

    for function in model.function_interpretations:
        rel_name = function_name_to_relation_name(function)
        relation_interpretations[rel_name] = set()
        for args, out in model.function_interpretations[function].items():
            relation_interpretations[rel_name].add((out, *args))

    return Model(
        universe,
        constant_interpretations,
        relation_interpretations,
        function_interpretations,
    )


def replace_relations_with_functions_in_model(
    model: Model[T], original_functions: AbstractSet[str]
) -> Union[Model[T], None]:
    """Converts the given model with no function interpretations to a
    canonically corresponding model with interpretations for the given function
    names, having each new function interpretation replace a canonically
    corresponding relation interpretation.

    Parameters:
        model: model to convert, that contains no function interpretations.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has an interpretation in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    assert len(model.function_interpretations) == 0
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_interpretations
        assert (
            function_name_to_relation_name(function)
            in model.relation_interpretations
        )
    # Task 8.2
    universe = model.universe
    constant_interpretations = model.constant_interpretations
    relation_interpretations = dict(model.relation_interpretations)

    function_interpretations = dict()

    for function in original_functions:
        rel_name = function_name_to_relation_name(function)
        if rel_name not in relation_interpretations:
            return None
        function_interpretations[function] = dict()
        arity = 0
        for out, *args in relation_interpretations[rel_name]:
            if tuple(args) in function_interpretations[function]:
                return None
            function_interpretations[function][tuple(args)] = out
            arity = len(args)
        if len(universe) ** arity != len(function_interpretations[function]):
            return None

        del relation_interpretations[rel_name]

    return Model(
        universe,
        constant_interpretations,
        relation_interpretations,
        function_interpretations,
    )


def _compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and which
            contains no variable names that are ``z`` followed by a number.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable name of the
        last returned step evaluates in that model to the value of the given
        term.
    """
    assert is_function(term.root)
    for variable in term.variables():
        assert not is_z_and_number(variable)
    # Task 8.3
    res = []

    def dfs(term):
        if not is_function(term.root):
            return term
        args = []
        for t in term.arguments:
            args.append(dfs(t))
        var_name = next(fresh_variable_name_generator)
        res.append(Formula("=", [Term(var_name), Term(term.root, args)]))
        return Term(var_name)

    dfs(term)
    return res


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function interpretations.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in this formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert (
        len(
            {
                function_name_to_relation_name(function)
                for function, arity in formula.functions()
            }.intersection(
                {relation for relation, arity in formula.relations()}
            )
        )
        == 0
    )
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    # Task 8.4
    result = None
    if is_equality(formula.root) or is_relation(formula.root):
        top_terms = []
        rel_list = []
        for term in formula.arguments:
            if not is_function(term.root):  # consant of variable
                top_terms.append(term)
            else:
                eqs = _compile_term(term)
                top_terms.append(eqs[-1].arguments[0])
                for eq in eqs:
                    rel_name = function_name_to_relation_name(
                        eq.arguments[1].root
                    )
                    left = eq.arguments[0]
                    right = eq.arguments[1]
                    rel = Formula(rel_name, [left, *right.arguments])
                    rel_list.append(rel)
        res = Formula(formula.root, top_terms)
        for rel in reversed(rel_list):
            var = rel.arguments[0]
            res = Formula("E", var.root, Formula("&", rel, res))
        result = res
    elif is_unary(formula.root):
        result = Formula(
            "~", replace_functions_with_relations_in_formula(formula.first)
        )
    elif is_binary(formula.root):
        result = Formula(
            formula.root,
            replace_functions_with_relations_in_formula(formula.first),
            replace_functions_with_relations_in_formula(formula.second),
        )
    elif is_quantifier(formula.root):
        result = Formula(
            formula.root,
            formula.variable,
            replace_functions_with_relations_in_formula(formula.statement),
        )
    return result


def replace_functions_with_relations_in_formulas(
    formulas: AbstractSet[Formula],
) -> Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function interpretations.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with interpretations for the functions
       names of the former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, which contain no variable names that are
            ``z`` followed by a number, and such that there exist no canonically
            corresponding function name and relation name that are both invoked
            in these formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas hold in a model `model` if and only if the
           returned formulas hold in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas hold in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert (
        len(
            set.union(
                *[
                    {
                        function_name_to_relation_name(function)
                        for function, arity in formula.functions()
                    }
                    for formula in formulas
                ]
            ).intersection(
                set.union(
                    *[
                        {relation for relation, arity in formula.relations()}
                        for formula in formulas
                    ]
                )
            )
        )
        == 0
    )
    for formula in formulas:
        for variable in formula.variables():
            assert not is_z_and_number(variable)
    # Task 8.5
    res = []
    relations = []
    for formula in formulas:
        func_free = replace_functions_with_relations_in_formula(formula)
        res.append(func_free)
        for func, arities in formula.functions():
            relations.append(
                (function_name_to_relation_name(func), arities + 1)
            )
    for rel in relations:
        restrict = _build_bimap_restrict(*rel)
        res.append(restrict)
    return res


def _build_bimap_restrict(rel_name, arity):
    shares = [next(fresh_variable_name_generator) for i in range(arity - 1)]
    shares_terms = [Term(z) for z in shares]
    z1, z2 = [next(fresh_variable_name_generator) for i in range(2)]
    consequent = Formula("=", [Term(z1), Term(z2)])
    premise = Formula(
        "&",
        Formula(rel_name, [Term(z1), *shares_terms]),
        Formula(rel_name, [Term(z2), *shares_terms]),
    )
    state = Formula("->", premise, consequent)
    for var in shares + [z1, z2]:
        state = Formula("A", var, state)

    exist_restrict = Formula(rel_name, [Term(z1), *shares_terms])
    exist_restrict = Formula("E", z1, exist_restrict)
    for var in shares:
        exist_restrict = Formula("A", var, exist_restrict)

    return Formula("&", state, exist_restrict)


def replace_equality_with_SAME_in_formulas(
    formulas: AbstractSet[Formula],
) -> Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model of the returned formulas, the
       interpretation of the relation name ``'SAME'`` is reflexive,
       symmetric, and transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model of the returned formulas, the interpretation of this
       relation name respects the interpretation of the relation name
       ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert "SAME" not in {
            relation for relation, arity in formula.relations()
        }
    # Task 8.6
    res = []
    relations = []
    for formula in formulas:
        eq_free = replace_equality_with_SAME_in_formula(formula)
        res.append(eq_free)
        for rel, arities in formula.relations():
            if arities > 0:
                relations.append((rel, arities))

    res.extend(_build_SAME_general_restrict())

    for rel in relations:
        restrict = _build_SAME_restrict(*rel)
        res.append(restrict)
    return res


def replace_equality_with_SAME_in_formula(formula):
    if is_equality(formula.root):
        return Formula("SAME", formula.arguments)
    elif is_relation(formula.root):
        return formula
    elif is_unary(formula.root):
        return Formula(
            "~", replace_equality_with_SAME_in_formula(formula.first)
        )
    elif is_binary(formula.root):
        return Formula(
            formula.root,
            replace_equality_with_SAME_in_formula(formula.first),
            replace_equality_with_SAME_in_formula(formula.second),
        )
    elif is_quantifier(formula.root):
        return Formula(
            formula.root,
            formula.variable,
            replace_equality_with_SAME_in_formula(formula.statement),
        )


def _build_SAME_general_restrict():
    reflexivity = Formula("A", "x", Formula("SAME", [Term("x"), Term("x")]))
    xy = Formula("SAME", [Term("x"), Term("y")])
    yx = Formula("SAME", [Term("y"), Term("x")])
    xyyx = Formula("->", xy, yx)
    yxxy = Formula("->", yx, xy)
    symmetry = Formula("A", "x", Formula("A", "y", Formula("&", xyyx, yxxy)))
    yz = Formula("SAME", [Term("y"), Term("z")])
    xz = Formula("SAME", [Term("x"), Term("z")])
    xy_yz = Formula("&", xy, yz)
    xy_yzxz = Formula("->", xy_yz, xz)
    transitivity = Formula(
        "A", "x", Formula("A", "y", Formula("A", "z", xy_yzxz))
    )
    return [reflexivity, symmetry, transitivity]


def _build_SAME_restrict(rel_name, arity):
    shares = [next(fresh_variable_name_generator) for i in range(2 * arity)]
    terms = [Term(z) for z in shares]
    consequent = Formula(
        "->",
        Formula(rel_name, terms[:arity]),
        Formula(rel_name, terms[arity:]),
    )
    premise = Formula("SAME", [terms[0], terms[arity]])
    for a, b in zip(terms[1:arity], terms[arity + 1 :]):
        premise = Formula("&", premise, Formula("SAME", [a, b]))

    state = Formula("->", premise, consequent)
    for var in shares:
        state = Formula("A", var, state)

    return state


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds an interpretation of the relation name ``'SAME'`` in the given
    model, that canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no interpretation of the relation name
            ``'SAME'``, to add the interpretation to.

    Returns:
        A model obtained from the given model by adding an interpretation of the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert "SAME" not in model.relation_interpretations
    # Task 8.7
    universe = model.universe
    constant_interpretations = model.constant_interpretations
    relation_interpretations = dict(model.relation_interpretations)
    function_interpretations = model.function_interpretations
    relation_interpretations["SAME"] = set()

    for var in universe:
        relation_interpretations["SAME"].add((var, var))

    return Model(
        universe,
        constant_interpretations,
        relation_interpretations,
        function_interpretations,
    )


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    interpretation of ``'SAME'`` in the given model, in the sense that any set
    of formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function interpretations, and
            contains an interpretation of the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the
            interpretations of all other relation names.

    Returns:
        A model that is a model of any set `formulas` if and only if the given
        model is a model of
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        interpretation of ``'SAME'`` in the given model.
    """
    assert (
        "SAME" in model.relation_interpretations
        and model.relation_arities["SAME"] == 2
    )
    assert len(model.function_interpretations) == 0
    # Task 8.8
    universe = model.universe
    constant_interpretations = model.constant_interpretations
    relation_interpretations = dict(model.relation_interpretations)
    same = relation_interpretations["SAME"]

    unionfind = {u: u for u in universe}

    def find_root(a):
        while unionfind[a] != a:
            a = unionfind[a]
        return a

    for a, b in same:
        root_b = find_root(b)
        if find_root(a) != root_b:
            unionfind[a] = root_b

    new_universe = set()
    for ele in universe:
        if unionfind[ele] == ele:
            new_universe.add(ele)

    new_constant = {}
    for const, interpretation in constant_interpretations.items():
        new_constant[const] = find_root(interpretation)

    new_relation = {}
    for rel, interpretation in relation_interpretations.items():
        if rel == "SAME":
            continue
        new_relation[rel] = set()
        for args in interpretation:
            new_relation[rel].add(tuple(find_root(x) for x in args))

    return Model(
        new_universe,
        new_constant,
        new_relation,
        model.function_interpretations,
    )
