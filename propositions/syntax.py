# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method


@lru_cache(maxsize=100)  # Cache the return value of is_variable
def is_variable(string: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return (
        string[0] >= "p"
        and string[0] <= "z"
        and (len(string) == 1 or string[1:].isdecimal())
    )


@lru_cache(maxsize=100)  # Cache the return value of is_constant
def is_constant(string: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return string == "T" or string == "F"


@lru_cache(maxsize=100)  # Cache the return value of is_unary
def is_unary(string: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return string == "~"


@lru_cache(maxsize=100)  # Cache the return value of is_binary
def is_binary(string: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        string: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # return string == '&' or string == '|' or string == '->'
    # For Chapter 3:
    return string in {"&", "|", "->", "+", "<->", "-&", "-|"}


@frozen
class Formula:
    """An immutable propositional formula in tree representation, composed from
    variable names, and operators applied to them.

    Attributes:
        root (`str`): the constant, variable name, or operator at the root of
            the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand of the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand of the
            root, if the root is a binary operator.
    """

    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(
        self,
        root: str,
        first: Optional[Formula] = None,
        second: Optional[Formula] = None,
    ):
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand for the root, if the root is a unary or
                binary operator.
            second: the second operand for the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        elif is_unary(self.root):
            return self.root + repr(self.first)
        return f"({repr(self.first)}{self.root}{repr(self.second)})"

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        # Task 1.2
        res = set()

        def dfs(formula):
            if is_constant(formula.root):
                return
            if is_variable(formula.root):
                res.add(formula.root)
                return
            if hasattr(formula, "first"):
                dfs(formula.first)
            if hasattr(formula, "second"):
                dfs(formula.second)

        dfs(self)
        return res

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        res = set()

        def dfs(formula):
            if is_variable(formula.root):
                return
            else:
                res.add(formula.root)
                if hasattr(formula, "first"):
                    dfs(formula.first)
                if hasattr(formula, "second"):
                    dfs(formula.second)

        dfs(self)
        return res

    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a variable name (e.g.,
            ``'x12'``) or a unary operator followed by a variable name, then the
            parsed prefix will include that entire variable name (and not just a
            part of it, such as ``'x1'``). If no prefix of the given string is a
            valid standard string representation of a formula then returned pair
            should be of ``None`` and an error message, where the error message
            is a string with some human-readable content.
        """
        # Task 1.4
        if string == "":
            return None, "Empty Formula Error"
        if string[0] != "(":
            if is_constant(string[0]):  # T or F
                return Formula(string[0]), string[1:]
            if is_unary(string[0]):  # ~
                f, remain = Formula._parse_prefix(string[1:])
                if f is None:
                    return None, "Unary Syntax Error"
                return Formula("~", f), remain
            if not is_variable(string[0]):
                return None, "Variable Sytax Error"

            # read variable
            n = len(string)
            v_end = n
            for i in range(1, n):
                if not string[i].isdecimal():
                    return Formula(string[:i]), string[i:]
            return Formula(string), ""
        else:
            # get first ()
            left_b = 0
            for i, ele in enumerate(string):
                if ele == "(":
                    left_b += 1
                elif ele == ")":
                    left_b -= 1
                if left_b == 0:
                    break

            f1, remain = Formula._parse_prefix(string[1:i])
            if f1 is None:
                return None, remain
            if not remain or (
                remain[0] not in ["|", "&", "+"]
                and remain[:2] not in ["->", "-&", "-|"]
                and remain[:3] not in ["<->"]
            ):
                return None, "binary syntax Error"
            if remain[0] in ["|", "&", "+"]:
                root = remain[0]
                f2, remain = Formula._parse_prefix(remain[1:])
                if remain != "":
                    return (
                        None,
                        f"Error: {string[:i+1]} is Not a valid formula",
                    )
                return Formula(root, f1, f2), string[i + 1 :]
            if remain[:1] == "-":
                operator = remain[:2]
                f2, remain = Formula._parse_prefix(remain[2:])
                if remain != "":
                    return (
                        None,
                        f"Error: {string[:i+1]} is Not a valid formula",
                    )
                return Formula(operator, f1, f2), string[i + 1 :]
            if remain[:1] == "<":
                operator = remain[:3]
                f2, remain = Formula._parse_prefix(remain[3:])
                if remain != "":
                    return (
                        None,
                        f"Error: {string[:i+1]} is Not a valid formula",
                    )
                return Formula(operator, f1, f2), string[i + 1 :]

    @staticmethod
    def is_formula(string: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            string: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        f, remain = Formula._parse_prefix(string)
        if f is None:
            return False
        # if is_variable(f.root) or is_constant(f.root) or is_unary(f.root):
        return remain == ""

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(string)
        # Task 1.6
        f, remain = Formula._parse_prefix(string)
        return f

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

        def dfs(formula):
            if is_constant(formula.root) or is_variable(formula.root):
                return formula.root
            if is_unary(formula.root):
                return formula.root + dfs(formula.first)
            assert formula.first and formula.second
            return formula.root + dfs(formula.first) + dfs(formula.second)

        return dfs(self)

    @staticmethod
    def parse_polish(string: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            string: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8
        f, remain = Formula._parse_polish_prefix(string)
        return f

    def _parse_polish_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        if string == "":
            return None, "Empty Formula Error"

        if is_constant(string[0]):  # T or F
            return Formula(string[0]), string[1:]

        if is_unary(string[0]):  # ~
            f, remain = Formula._parse_polish_prefix(string[1:])
            if f is None:
                return None, "Unary Syntax Error"
            return Formula("~", f), remain

        if is_variable(string[0]):
            # read variable
            n = len(string)
            v_end = n
            for i in range(1, n):
                if not string[i].isdecimal():
                    return Formula(string[:i]), string[i:]
            return Formula(string), ""

        if string[0] in ["|", "&"]:
            f1, remain = Formula._parse_polish_prefix(string[1:])
            if f1 is None:
                return None, remain
            root = string[0]
            f2, remain = Formula._parse_polish_prefix(remain)
            # different from parser_prefix
            # if remain != "":
            #     return None, f"Error: {string} is Not a valid formula"
            return Formula(root, f1, f2), remain

        if string[:2] == "->":
            f1, remain = Formula._parse_polish_prefix(string[2:])
            if f1 is None:
                return None, remain
            root = "->"
            f2, remain = Formula._parse_polish_prefix(remain)
            # if remain != "":
            #     return None, f"Error: {string} is Not a valid formula"
            return Formula(root, f1, f2), remain

        return None, "Error"

    def substitute_variables(
        self, substitution_map: Mapping[str, Formula]
    ) -> Formula:
        """Substitutes in the current formula, each variable name `v` that is a
        key in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            variable name occurrences originating in the current formula are
            substituted (i.e., variable name occurrences originating in one of
            the specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((p->p)|r)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
            (((q&r)->(q&r))|p)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3
        if is_variable(self.root) and self.root in substitution_map:
            return substitution_map[self.root]
        if is_binary(self.root):
            first = self.first.substitute_variables(substitution_map)
            second = self.second.substitute_variables(substitution_map)
            return Formula(self.root, first, second)
        elif is_unary(self.root):
            first = self.first.substitute_variables(substitution_map)
            return Formula(self.root, first)
        return self

    def substitute_operators(
        self, substitution_map: Mapping[str, Formula]
    ) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.

        Returns:
            The formula resulting from performing all substitutions. Only
            operator occurrences originating in the current formula are
            substituted (i.e., operator occurrences originating in one of the
            specified substitutions are not subjected to additional
            substitutions).

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert (
                is_constant(operator)
                or is_unary(operator)
                or is_binary(operator)
            )
            assert substitution_map[operator].variables().issubset({"p", "q"})
        # Task 3.4

        if is_constant(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]
            return self
        elif is_unary(self.root):
            if self.root in substitution_map:
                var_map = {
                    "p": self.first.substitute_operators(substitution_map)
                }
                return substitution_map[self.root].substitute_variables(
                    var_map
                )
            else:
                return Formula(
                    self.root,
                    self.first.substitute_operators(substitution_map),
                )
        elif is_binary(self.root):
            if self.root in substitution_map:
                first = self.first.substitute_operators(substitution_map)
                second = self.second.substitute_operators(substitution_map)
                var_map = {"p": first, "q": second}
                return substitution_map[self.root].substitute_variables(
                    var_map
                )
            else:
                return Formula(
                    self.root,
                    self.first.substitute_operators(substitution_map),
                    self.second.substitute_operators(substitution_map),
                )
        elif is_variable(self.root):
            return self
