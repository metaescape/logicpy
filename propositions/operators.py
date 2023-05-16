# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    substitution_map = {"F": Formula("&", Formula("p"),
                                     Formula("~", Formula("p"))), 
                        "T": Formula("|", Formula("p"),
                                     Formula("~", Formula("p"))),
                        "+": Formula("&",
                                        Formula("|",
                                                Formula("p"),
                                                Formula("q")),
                                        Formula("|",
                                                Formula("~", Formula("p")),
                                                Formula("~", Formula("q")))),
                        "<->": Formula("|",
                                        Formula("&",
                                                Formula("p"),
                                                Formula("q")),
                                        Formula("&",
                                                Formula("~", Formula("p")),
                                                Formula("~", Formula("q")))),
                        "-&": Formula("~", Formula("&",
                                                Formula("p"),
                                                Formula("q"))),
                        "-|": Formula("~", Formula("|",
                                                Formula("p"),
                                                Formula("q"))),
                        "->": Formula("|", Formula("~", Formula("p")),
                                           Formula("q"))
                        }
    
    return formula.substitute_operators(substitution_map)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    substitution_map = {
                        "|": Formula("~", 
                                     Formula("&",
                                             Formula("~", Formula("p")),
                                             Formula("~", Formula("q"))))
                        }
    
    return to_not_and_or(formula).substitute_operators(substitution_map)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    to_not_nand_map = {
                        "&": Formula("~", Formula("-&", Formula("p"), Formula("q")))
                      }

    substitution_map = {
                        "~": Formula("-&", Formula("p"), Formula("p")),
                        }
    
    return to_not_and(formula).substitute_operators(to_not_nand_map).substitute_operators(substitution_map)


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    substitution_map = {
                        "&": Formula("~", Formula("->", Formula("p"),
                                                  Formula("~", Formula("q"))))
                        }
    
    return to_not_and(formula).substitute_operators(substitution_map)



def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    substitution_map = {
                        "~": Formula("->", Formula("p"), Formula("F")),
                        }
    
    return to_implies_not(formula).substitute_operators(substitution_map)
