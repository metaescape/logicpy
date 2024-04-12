# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator, is_z_and_number

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for Predicate Logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(
        Formula.parse("((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))"),
        {"x", "R"},
    ),
    Schema(
        Formula.parse("((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))"),
        {"x", "R"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&"
            "(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&"
            "(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&"
            "(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&"
            "(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&"
            "(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&"
            "(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&"
            "(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&"
            "(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&"
            "(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&"
            "(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&"
            "(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&"
            "(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))"
        ),
        {"x", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((R(x)->Q(x))&(Q(x)->R(x)))->"
            "((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))"
        ),
        {"x", "y", "R", "Q"},
    ),
    Schema(
        Formula.parse(
            "(((R(x)->Q(x))&(Q(x)->R(x)))->"
            "((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))"
        ),
        {"x", "y", "R", "Q"},
    ),
)


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    # Task 11.3a
    root = formula.root
    if is_quantifier(root):
        return False
    if is_equality(root) or is_relation(root):
        return True
    if is_unary(root):
        return is_quantifier_free(formula.first)
    if is_binary(root):
        return is_quantifier_free(formula.first) and is_quantifier_free(
            formula.second
        )
    return True


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    # Task 11.3b
    if is_quantifier_free(formula):
        return True
    if not is_quantifier(formula.root):
        return False
    return is_in_prenex_normal_form(formula.statement)


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula(
        "&",
        Formula("->", formula1, formula2),
        Formula("->", formula2, formula1),
    )


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both bound and
        free occurrences or is quantified by more than one quantifier, ``True``
        otherwise.

    Examples:
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ax[R(x)]|Ey[R(y)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(y=0&(Ax[R(x)]|Ex[R(x)]))'))
        False
        >>> has_uniquely_named_variables(
        ...     Formula.parse('(x=0&(Ay[R(y)]|Ez[R(z)]))'))
        True
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(
                formula.first
            ) and has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.statement)
        else:
            assert is_equality(formula.root) or is_relation(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def _uniquely_rename_quantified_variables(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = _uniquely_rename_quantified_variables(
        ...     formula)
        >>> returned_formula
        ~(w=x|Az58[(Ez17[(z17=z58&Az4[z4=z17])]->Az32[z32=y])])
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    # Task 11.5

    root = formula.root
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if is_unary(root):
        returned_formula, proof = _uniquely_rename_quantified_variables(
            formula.first
        )
        new_formula = Formula("~", returned_formula)

        eqv_formula = equivalence_of(formula.first, returned_formula)

        eqv_idx = prover.add_proof(eqv_formula, proof)
        res_formula = equivalence_of(formula, new_formula)
        prover.add_tautological_implication(res_formula, {eqv_idx})

        return new_formula, prover.qed()
    if is_binary(root):
        returned_formula1, proof1 = _uniquely_rename_quantified_variables(
            formula.first
        )
        returned_formula2, proof2 = _uniquely_rename_quantified_variables(
            formula.second
        )

        eqv_formula1 = equivalence_of(formula.first, returned_formula1)
        eqv_idx1 = prover.add_proof(eqv_formula1, proof1)
        eqv_formula2 = equivalence_of(formula.second, returned_formula2)
        eqv_idx2 = prover.add_proof(eqv_formula2, proof2)

        eqv_formula = equivalence_of(
            formula, Formula(root, returned_formula1, returned_formula2)
        )
        prover.add_tautological_implication(eqv_formula, {eqv_idx1, eqv_idx2})

        new_formula = Formula(root, returned_formula1, returned_formula2)

        return new_formula, prover.qed()
    if is_quantifier(root):

        statement = formula.statement

        return_statement, q_proof = _uniquely_rename_quantified_variables(
            statement
        )
        new_variable = next(fresh_variable_name_generator)
        new_statement = return_statement.substitute(
            {str(formula.variable): Term(new_variable)}
        )
        new_formula = Formula(
            root,
            new_variable,
            new_statement,
        )
        left = equivalence_of(statement, return_statement)
        right = equivalence_of(formula, new_formula)

        _axiom = Formula("->", left, right)

        inner_eqv_idx = prover.add_proof(left, q_proof)
        idx = -1 if root == "E" else -2
        template = statement.substitute({str(formula.variable): Term("_")})
        new_template = new_statement.substitute({new_variable: Term("_")})
        # print(_axiom)
        # print(template)
        # print(new_statement)
        # print(formula.variable)
        # print(new_template)
        axiom_idx = prover.add_instantiated_assumption(
            _axiom,
            ADDITIONAL_QUANTIFICATION_AXIOMS[idx],
            {
                "x": formula.variable,
                "R": template,
                "y": new_variable,
                "Q": new_template,
            },
        )
        prover.add_mp(right, inner_eqv_idx, axiom_idx)

        # reference
        Schema(
            Formula.parse(
                "(((R(x)->Q(x))&(Q(x)->R(x)))->"
                "((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))"
            ),
            {"x", "y", "R", "Q"},
        )

        Schema(
            Formula.parse(
                "(((R(x)->Q(x))&(Q(x)->R(x)))->"
                "((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))"
            ),
            {"x", "y", "R", "Q"},
        )

        return new_formula, prover.qed()

    # is_relation or is_equality without rename
    prover.add_tautology(equivalence_of(formula, formula))
    return formula, prover.qed()


def _pull_out_quantifications_across_negation(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = _pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6

    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))

    root = formula.root
    if not is_quantifier(formula.first.root):
        # base case
        tautology = equivalence_of(formula, formula)
        prover.add_tautology(tautology)
        return formula, prover.qed()

    subformula = Formula("~", formula.first.statement)
    target_formula, proof = _pull_out_quantifications_across_negation(
        subformula
    )  # target_formula: ~P(x)

    quantifier = "E" if formula.first.root == "A" else "A"
    variable = formula.first.variable

    qx_subformula = Formula(quantifier, variable, subformula)
    qx_target_formula = Formula(quantifier, variable, target_formula)

    # use extra axiom 15/16
    idx = -1 if quantifier == "E" else -2

    left = equivalence_of(subformula, target_formula)
    right = equivalence_of(qx_subformula, qx_target_formula)
    inner_eq = prover.add_proof(left, proof)

    _axiom = Formula("->", left, right)
    template_R = subformula.substitute({variable: Term("_")})
    template_Q = target_formula.substitute({variable: Term("_")})
    axiom_idx = prover.add_instantiated_assumption(
        _axiom,
        ADDITIONAL_QUANTIFICATION_AXIOMS[idx],
        {"R": template_R, "x": variable, "Q": template_Q, "y": variable},
    )

    eq1 = prover.add_mp(right, inner_eq, axiom_idx)

    # reference axiom 1/2
    idx = 0 if quantifier == "E" else 1

    _axiom = equivalence_of(formula, qx_subformula)
    eq2 = prover.add_instantiated_assumption(
        _axiom,
        ADDITIONAL_QUANTIFICATION_AXIOMS[idx],
        {"R": template_R.first, "x": variable},
    )

    prover.add_tautological_implication(
        equivalence_of(formula, qx_target_formula), {eq1, eq2}
    )

    Schema(
        Formula.parse("((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))"),
        {"x", "R"},
    )
    Schema(
        Formula.parse("((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))"),
        {"x", "R"},
    )

    return qx_target_formula, prover.qed()


def _pull_out_quantifications_from_left_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7a


def _pull_out_quantifications_from_right_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7b


def _pull_out_quantifications_across_binary_operator(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = _pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8


def _to_prenex_normal_form_from_uniquely_named_variables(
    formula: Formula,
) -> Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = _to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    # Task 11.9


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names that are
            ``z`` followed by a number.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~(w=x|Aw[(Ex[(x=w&Aw[w=x])]->Ax[x=y])])')
        >>> returned_formula, proof = to_prenex_normal_form(formula)
        >>> returned_formula
        Ez58[Ez17[Az4[Ez32[~(w=x|((z17=z58&z4=z17)->z32=y))]]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    for variable in formula.variables():
        assert not is_z_and_number(variable)
    # Task 11.10
