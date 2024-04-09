# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: predicates/some_proofs.py

"""Some proofs in Predicate Logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
from predicates.deduction import *
from predicates.prenex import equivalence_of


def prove_syllogism(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Man(aristotle)"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_instantiated_assumption(
        "(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))",
        Prover.UI,
        {"R": "(Man(_)->Mortal(_))", "c": "aristotle"},
    )
    step3 = prover.add_mp("(Man(aristotle)->Mortal(aristotle))", step1, step2)
    step4 = prover.add_assumption("Man(aristotle)")
    step5 = prover.add_mp("Mortal(aristotle)", step4, step3)
    return prover.qed()


def prove_syllogism_with_universal_instantiation(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Man(aristotle)"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_universal_instantiation(
        "(Man(aristotle)->Mortal(aristotle))", step1, "aristotle"
    )
    step3 = prover.add_assumption("Man(aristotle)")
    step4 = prover.add_mp("Mortal(aristotle)", step3, step2)
    return prover.qed()


def prove_syllogism_all_all(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Greek(x)->Human(x))]", "Ax[(Human(x)->Mortal(x))]"},
        print_as_proof_forms,
    )
    step1 = prover.add_assumption("Ax[(Greek(x)->Human(x))]")
    step2 = prover.add_universal_instantiation(
        "(Greek(x)->Human(x))", step1, "x"
    )
    step3 = prover.add_assumption("Ax[(Human(x)->Mortal(x))]")
    step4 = prover.add_universal_instantiation(
        "(Human(x)->Mortal(x))", step3, "x"
    )
    step5 = prover.add_tautology(
        "((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))"
    )
    step6 = prover.add_mp(
        "((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))", step2, step5
    )
    step7 = prover.add_mp("(Greek(x)->Mortal(x))", step4, step6)
    step8 = prover.add_ug("Ax[(Greek(x)->Mortal(x))]", step7)
    return prover.qed()


def prove_syllogism_all_all_with_tautological_implication(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Greek(x)->Human(x))]", "Ax[(Human(x)->Mortal(x))]"},
        print_as_proof_forms,
    )
    step1 = prover.add_assumption("Ax[(Greek(x)->Human(x))]")
    step2 = prover.add_universal_instantiation(
        "(Greek(x)->Human(x))", step1, "x"
    )
    step3 = prover.add_assumption("Ax[(Human(x)->Mortal(x))]")
    step4 = prover.add_universal_instantiation(
        "(Human(x)->Mortal(x))", step3, "x"
    )
    step5 = prover.add_tautological_implication(
        "(Greek(x)->Mortal(x))", {step2, step4}
    )
    step6 = prover.add_ug("Ax[(Greek(x)->Mortal(x))]", step5)
    return prover.qed()


def prove_syllogism_all_exists(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Ex[Man(x)]"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_assumption("Ex[Man(x)]")
    step3 = prover.add_universal_instantiation(
        "(Man(x)->Mortal(x))", step1, "x"
    )
    step4 = prover.add_instantiated_assumption(
        "(Mortal(x)->Ex[Mortal(x)])", Prover.EI, {"R": "Mortal(_)", "c": "x"}
    )
    step5 = prover.add_tautological_implication(
        "(Man(x)->Ex[Mortal(x)])", {step3, step4}
    )
    step6 = prover.add_ug("Ax[(Man(x)->Ex[Mortal(x)])]", step5)
    step7 = prover.add_instantiated_assumption(
        "((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])",
        Prover.ES,
        {"R": "Man(_)", "Q": "Ex[Mortal(x)]"},
    )
    step8 = prover.add_tautological_implication(
        "Ex[Mortal(x)]", {step2, step6, step7}
    )
    return prover.qed()


def prove_syllogism_all_exists_with_existential_derivation(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)

    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof, created with the help of the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[(Man(x)->Mortal(x))]", "Ex[Man(x)]"}, print_as_proof_forms
    )
    step1 = prover.add_assumption("Ax[(Man(x)->Mortal(x))]")
    step2 = prover.add_assumption("Ex[Man(x)]")
    step3 = prover.add_universal_instantiation(
        "(Man(x)->Mortal(x))", step1, "x"
    )
    step4 = prover.add_instantiated_assumption(
        "(Mortal(x)->Ex[Mortal(x)])", Prover.EI, {"R": "Mortal(_)", "c": "x"}
    )
    step5 = prover.add_tautological_implication(
        "(Man(x)->Ex[Mortal(x)])", {step3, step4}
    )
    step6 = prover.add_existential_derivation("Ex[Mortal(x)]", step2, step5)
    return prover.qed()


def prove_lovers(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)

    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(
        {"Ax[Ey[Loves(x,y)]]", "Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]"},
        print_as_proof_forms,
    )
    # Task 10.4

    step1 = prover.add_assumption("Ax[Ey[Loves(x,y)]]")
    step2 = prover.add_universal_instantiation("Ey[Loves(x,y)]", step1, "x")
    step3 = prover.add_assumption("Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]")
    step4 = prover.add_universal_instantiation(
        "Az[Ay[(Loves(x,y)->Loves(z,x))]]", step3, "x"
    )
    step4 = prover.add_universal_instantiation(
        "Ay[(Loves(x,y)->Loves(z,x))]", step4, "z"
    )
    step5 = prover.add_universal_instantiation(
        "(Loves(x,y)->Loves(z,x))", step4, "y"
    )
    step6 = prover.add_existential_derivation("Loves(z,x)", step2, step5)
    step7 = prover.add_ug("Az[Loves(z,x)]", step6)
    step8 = prover.add_ug("Ax[Az[Loves(z,x)]]", step7)

    return prover.qed()


def prove_homework(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)

    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """

    prover = Prover(
        {"~Ex[(Homework(x)&Fun(x))]", "Ex[(Homework(x)&Reading(x))]"},
        print_as_proof_forms,
    )
    # Task 10.5
    step1 = prover.add_assumption("~Ex[(Homework(x)&Fun(x))]")

    step2 = prover.add_instantiated_assumption(
        "((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])",
        Prover.EI,
        {"R": "(Homework(_)&Fun(_))", "c": "x"},
    )

    step3 = prover.add_tautological_implication(
        "(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))", {step2}
    )

    step4 = prover.add_mp("~(Homework(x)&Fun(x))", step1, step3)
    step5 = prover.add_tautological_implication(
        "(Homework(x)->~Fun(x))", {step4}
    )
    step6 = prover.add_tautological_implication(
        "((Homework(x)&Reading(x))->(~Fun(x)&Reading(x)))", {step5}
    )
    step7 = prover.add_tautological_implication(
        "((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))", {step6}
    )
    # can replace step3 to  step7 with following line:
    # step7 = prover.add_tautological_implication(
    #     "((Homework(x)&Reading(x))->(Reading(x)&~Fun(x)))", {step1, step2}
    # )

    step8 = prover.add_instantiated_assumption(
        "((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])",
        Prover.EI,
        {"R": "(Reading(_)&~Fun(_))", "c": "x"},
    )

    step9 = prover.add_assumption("Ex[(Homework(x)&Reading(x))]")
    step10 = prover.add_tautological_implication(
        "((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])", {step7, step8}
    )

    step11 = prover.add_existential_derivation(
        "Ex[(Reading(x)&~Fun(x))]", step9, step10
    )
    return prover.qed()


#: The three group axioms
GROUP_AXIOMS = frozenset(
    {
        "plus(0,x)=x",
        "plus(minus(x),x)=0",
        "plus(plus(x,y),z)=plus(x,plus(y,z))",
    }
)


def prove_group_right_neutral(
    stop_before_flipped_equality: bool,
    stop_before_free_instantiation: bool,
    stop_before_substituted_equality: bool,
    stop_before_chained_equality: bool,
    print_as_proof_forms: bool = False,
) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof created up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof created up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof created up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof created up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption("plus(0,x)=x")
    negation = prover.add_assumption("plus(minus(x),x)=0")
    associativity = prover.add_assumption(
        "plus(plus(x,y),z)=plus(x,plus(y,z))"
    )
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality("x=plus(0,x)", zero)
    flipped_negation = prover.add_flipped_equality(
        "0=plus(minus(x),x)", negation
    )
    flipped_associativity = prover.add_flipped_equality(
        "plus(x,plus(y,z))=plus(plus(x,y),z)", associativity
    )
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        "0=plus(minus(minus(x)),minus(x))", flipped_negation, {"x": "minus(x)"}
    )
    step8 = prover.add_flipped_equality(
        "plus(minus(minus(x)),minus(x))=0", step7
    )
    step9 = prover.add_free_instantiation(
        "plus(plus(minus(minus(x)),minus(x)),x)="
        "plus(minus(minus(x)),plus(minus(x),x))",
        associativity,
        {"x": "minus(minus(x))", "y": "minus(x)", "z": "x"},
    )
    step10 = prover.add_free_instantiation("plus(0,0)=0", zero, {"x": "0"})
    step11 = prover.add_free_instantiation(
        "plus(x,0)=plus(0,plus(x,0))", flipped_zero, {"x": "plus(x,0)"}
    )
    step12 = prover.add_free_instantiation(
        "plus(0,plus(x,0))=plus(plus(0,x),0)",
        flipped_associativity,
        {"x": "0", "y": "x", "z": "0"},
    )
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        "plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)",
        step7,
        "plus(plus(_,x),0)",
    )
    step14 = prover.add_substituted_equality(
        "plus(plus(plus(minus(minus(x)),minus(x)),x),0)="
        "plus(plus(minus(minus(x)),plus(minus(x),x)),0)",
        step9,
        "plus(_,0)",
    )
    step15 = prover.add_substituted_equality(
        "plus(plus(minus(minus(x)),plus(minus(x),x)),0)="
        "plus(plus(minus(minus(x)),0),0)",
        negation,
        "plus(plus(minus(minus(x)),_),0)",
    )
    step16 = prover.add_free_instantiation(
        "plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))",
        associativity,
        {"x": "minus(minus(x))", "y": "0", "z": "0"},
    )
    step17 = prover.add_substituted_equality(
        "plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)",
        step10,
        "plus(minus(minus(x)),_)",
    )
    step18 = prover.add_substituted_equality(
        "plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))",
        flipped_negation,
        "plus(minus(minus(x)),_)",
    )
    step19 = prover.add_free_instantiation(
        "plus(minus(minus(x)),plus(minus(x),x))="
        "plus(plus(minus(minus(x)),minus(x)),x)",
        flipped_associativity,
        {"x": "minus(minus(x))", "y": "minus(x)", "z": "x"},
    )
    step20 = prover.add_substituted_equality(
        "plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)", step8, "plus(_,x)"
    )
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        "plus(x,0)=x",
        [
            step11,
            step12,
            step13,
            step14,
            step15,
            step16,
            step17,
            step18,
            step19,
            step20,
            zero,
        ],
    )
    return prover.qed()


def prove_group_unique_zero(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS.union({"plus(a,c)=a"}), print_as_proof_forms)
    # Task 10.10
    zero = prover.add_assumption("plus(0,x)=x")
    negation = prover.add_assumption("plus(minus(x),x)=0")
    associativity = prover.add_assumption(
        "plus(plus(x,y),z)=plus(x,plus(y,z))"
    )
    ac_a = prover.add_assumption("plus(a,c)=a")

    flipped_associativity = prover.add_flipped_equality(
        "plus(x,plus(y,z))=plus(plus(x,y),z)", associativity
    )

    # -x+(a+c)=(-x+a)
    step1 = prover.add_substituted_equality(
        "plus(minus(x),plus(a,c))=plus(minus(x),a)", ac_a, "plus(minus(x),_)"
    )

    # -a+(a+c)=(-a+a)
    step1_instance = prover.add_free_instantiation(
        "plus(minus(a),plus(a,c))=plus(minus(a),a)", step1, {"x": "a"}
    )

    # (-a+a) = -a+(a+c)
    flipped_step1 = prover.add_flipped_equality(
        "plus(minus(a),a)=plus(minus(a),plus(a,c))", step1_instance
    )

    # -a+(a+c) = (-a+a)+c
    step2 = prover.add_free_instantiation(
        "plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)",
        flipped_associativity,
        {"x": "minus(a)", "y": "a", "z": "c"},
    )

    # (-a+a) = 0
    step3 = prover.add_free_instantiation(
        "plus(minus(a),a)=0", negation, {"x": "a"}
    )

    # 0 = (-a+a)
    flipped_step3 = prover.add_flipped_equality("0=plus(minus(a),a)", step3)

    # (-a+a)+c = 0+c
    step4 = prover.add_substituted_equality(
        "plus(plus(minus(a),a),c)=plus(0,c)", step3, "plus(_,c)"
    )

    #  0+c=c
    step5 = prover.add_free_instantiation("plus(0,c)=c", zero, {"x": "c"})

    step6 = prover.add_chained_equality(
        "0=c", [flipped_step3, flipped_step1, step2, step4, step5]
    )

    step7 = prover.add_flipped_equality("c=0", step6)

    return prover.qed()


#: The six field axioms
FIELD_AXIOMS = frozenset(
    GROUP_AXIOMS.union(
        {
            "plus(x,y)=plus(y,x)",
            "times(x,1)=x",
            "times(x,y)=times(y,x)",
            "times(times(x,y),z)=times(x,times(y,z))",
            "(~x=0->Ey[times(y,x)=1])",
            "times(x,plus(y,z))=plus(times(x,y),times(x,z))",
        }
    )
)


def prove_field_zero_multiplication(
    print_as_proof_forms: bool = False,
) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # Task 10.11
    #  - 0+x=x -> 0+0=0
    # - 根据替换性，两边代入乘 x 操作，那么 x(0+0)=x0
    # - 根据分配率，那么 x0+x0=x0
    # - 类似 T10.10, 得到 x0=0
    # - 根据乘法交换律，0x=x0
    # - 根据等式传递性，0x=0

    zero = prover.add_assumption("plus(0,x)=x")

    # 0+0=0
    zero_zero = prover.add_free_instantiation("plus(0,0)=0", zero, {"x": "0"})

    # x(0+0)=x0
    x_zero = prover.add_substituted_equality(
        "times(x,plus(0,0))=times(x,0)", zero_zero, "times(x,_)"
    )

    times_distribution = prover.add_assumption(
        "times(x,plus(y,z))=plus(times(x,y),times(x,z))"
    )
    # x(0+0)=x0+x0
    x00 = prover.add_free_instantiation(
        "times(x,plus(0,0))=plus(times(x,0),times(x,0))",
        times_distribution,
        {"y": "0", "z": "0"},
    )
    # x0+x0=x(0+0)
    fipped_x00 = prover.add_flipped_equality(
        "plus(times(x,0),times(x,0))=times(x,plus(0,0))", x00
    )

    # x0+x0=x0
    x0_x0_x0 = prover.add_chained_equality(
        "plus(times(x,0),times(x,0))=times(x,0)", [fipped_x00, x_zero]
    )

    # adapt from T10.10
    negation = prover.add_assumption("plus(minus(x),x)=0")
    associativity = prover.add_assumption(
        "plus(plus(x,y),z)=plus(x,plus(y,z))"
    )

    flipped_associativity = prover.add_flipped_equality(
        "plus(x,plus(y,z))=plus(plus(x,y),z)", associativity
    )

    # -x+(a+c)=(-x+a)
    step1 = prover.add_substituted_equality(
        "plus(minus(times(x,0)),plus(times(x,0),times(x,0)))=plus(minus(times(x,0)),times(x,0))",
        x0_x0_x0,
        "plus(minus(times(x,0)),_)",
    )

    # (-a+a) = -a+(a+c)
    flipped_step1 = prover.add_flipped_equality(
        "plus(minus(times(x,0)),times(x,0))=plus(minus(times(x,0)),plus(times(x,0),times(x,0)))",
        step1,
    )

    # -a+(a+c) = (-a+a)+c
    step2 = prover.add_free_instantiation(
        "plus(minus(times(x,0)),plus(times(x,0),times(x,0)))=plus(plus(minus(times(x,0)),times(x,0)),times(x,0))",
        flipped_associativity,
        {"x": "minus(times(x,0))", "y": "times(x,0)", "z": "times(x,0)"},
    )

    # (-a+a) = 0
    step3 = prover.add_free_instantiation(
        "plus(minus(times(x,0)),times(x,0))=0", negation, {"x": "times(x,0)"}
    )

    # 0 = (-a+a)
    flipped_step3 = prover.add_flipped_equality(
        "0=plus(minus(times(x,0)),times(x,0))", step3
    )

    # (-a+a)+c = 0+c
    step4 = prover.add_substituted_equality(
        "plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(0,times(x,0))",
        step3,
        "plus(_,times(x,0))",
    )

    #  0+c=c
    step5 = prover.add_free_instantiation(
        "plus(0,times(x,0))=times(x,0)", zero, {"x": "times(x,0)"}
    )

    step6 = prover.add_chained_equality(
        "0=times(x,0)", [flipped_step3, flipped_step1, step2, step4, step5]
    )

    step7 = prover.add_flipped_equality("times(x,0)=0", step6)

    times_sym = prover.add_assumption("times(x,y)=times(y,x)")
    filpped_times_sym = prover.add_flipped_equality(
        "times(y,x)=times(x,y)", times_sym
    )
    step8 = prover.add_free_instantiation(
        "times(0,x)=times(x,0)", filpped_times_sym, {"y": "0"}
    )
    res = prover.add_chained_equality("times(0,x)=0", [step8, step7])

    return prover.qed()


#: Axiom schema of induction
INDUCTION_AXIOM = Schema(
    Formula.parse("((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])"), {"R"}
)
#: The seven axioms of Peano arithmetic
PEANO_AXIOMS = frozenset(
    {
        "(s(x)=s(y)->x=y)",
        "~s(x)=0",
        "plus(x,0)=x",
        "plus(x,s(y))=s(plus(x,y))",
        "times(x,0)=0",
        "times(x,s(y))=plus(times(x,y),x)",
        INDUCTION_AXIOM,
    }
)


def prove_peano_left_neutral(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)
    # Task 10.12
    zero = prover.add_assumption("plus(x,0)=x")

    # x+s(y) = s(x+y)
    plus_add = prover.add_assumption("plus(x,s(y))=s(plus(x,y))")

    ME = Schema(Formula.parse("(c=d->(R(c)->R(d)))"), {"R", "c", "d"})

    # begin to prove 0+x=x->s(0+x)=s(x)
    # 0+x=x->s(0+x)=s(0+x)->s(0+x)=s(x)
    me1 = prover.add_instantiated_assumption(
        "(plus(0,x)=x->(s(plus(0,x))=s(plus(0,x))->s(plus(0,x))=s(x)))",
        prover.ME,
        {"c": "plus(0,x)", "d": "x", "R": "s(plus(0,x))=s(_))"},
    )

    # s(0+x)=s(0+x)
    always = prover.add_instantiated_assumption(
        "s(plus(0,x))=s(plus(0,x))", prover.RX, {"c": "s(plus(0,x))"}
    )

    q = "(plus(0,x)=x->s(plus(0,x))=s(x))"  # 0+x=x -> s(0+x)=s(x)
    # 0+x=x -> s(0+x)=s(x)
    q_line = prover.add_tautological_implication(q, {me1, always})
    # end to prove 0+x=x->s(0+x)=s(x)

    # begin to prove 0+x=x -> 0+s(x)=s(x)

    # 0+s(x)=s(0+x)
    zero_add = prover.add_free_instantiation(
        "plus(0,s(x))=s(plus(0,x))", plus_add, {"x": "0", "y": "x"}
    )

    # s(0+x) = 0+s(x)
    p = "s(plus(0,x))=plus(0,s(x))"  # s(0+x) =0+s(x)
    p_line = prover.add_flipped_equality(p, zero_add)

    r = "(plus(0,x)=x->plus(0,s(x))=s(x))"  # 0+x=x -> 0+s(x)=s(x)
    # s(0+x)=0+s(x) -> (0+x=x -> s(0+x)=s(x)->0+x=x -> 0+s(x)=s(x))
    me2 = prover.add_instantiated_assumption(
        f"({p}->({q}->{r}))",
        prover.ME,
        {
            "c": "s(plus(0,x))",
            "d": "plus(0,s(x))",
            "R": "(plus(0,x)=x->_=s(x))",
        },
    )

    # prove q->r
    q_r_line = prover.add_mp(f"({q}->{r})", p_line, me2)

    # prove r :  0+x=x -> 0+s(x)=s(x)
    r_line = prover.add_mp(r, q_line, q_r_line)

    # end to prove 0+x=x -> 0+s(x)=s(x)

    # make induction step universal
    ug_r = prover.add_ug(f"Ax[{r}]", r_line)

    # base case and induction case
    # base case 0 + 0 = 0
    base_case = prover.add_free_instantiation("plus(0,0)=0", zero, {"x": "0"})
    condition = f"(plus(0,0)=0&Ax[{r}])"
    base_ind = prover.add_tautological_implication(
        condition, {base_case, ug_r}
    )
    ind_axiom = prover.add_instantiated_assumption(
        f"({condition}->Ax[plus(0,x)=x])",
        INDUCTION_AXIOM,
        {
            "R": f"plus(0,_)=_",
        },
    )
    ug_result = prover.add_mp("Ax[plus(0,x)=x]", base_ind, ind_axiom)
    result = prover.add_universal_instantiation(
        "plus(0,x)=x", ug_result, Term("x")
    )

    return prover.qed()


#: Axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse("Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]"), {"R"}
)


def prove_russell_paradox(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)
    # Task 10.13

    # A(x)[x \in y<->~x \in x]-> c\in y <-> ~c \in c

    # reference
    UI = Schema(Formula.parse("(Ax[R(x)]->R(c))"), {"R", "x", "c"})

    ui_first_temp = "((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))"
    ui_first = ui_first_temp.replace("y", "c")
    ui_second = ui_first_temp.replace("x", "c")

    specified_str = f"(Ax[{ui_first}]->{ui_second})"

    specified = prover.add_instantiated_assumption(
        specified_str,
        prover.UI,
        {
            "R": ui_first_temp.replace("x", "_"),
            "c": "c",
        },
    )

    ug = prover.add_ug(f"Ay[{specified_str}]", specified)

    comprehension_temp = "Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]"
    comprehension_str = comprehension_temp.replace("R(x)", "~In(x,x)")

    comprehension = prover.add_instantiated_assumption(
        comprehension_str,
        COMPREHENSION_AXIOM,
        {
            "R": "~In(_,_))",
        },
    )

    both = f"(Ay[{specified_str}]&{comprehension_str})"
    prover.add_tautological_implication(both, {ug, comprehension})

    es_str = f"({both}->Q())".replace("Q()", ui_second)
    print(es_str)

    # Referece
    ES = Schema(
        Formula.parse("((Ax[(R(x)->Q())]&Ex[R(x)])->Q())"), {"Q", "R", "x"}
    )
    prover.add_free_instantiation

    print(f"Ax[{ui_first_temp}]".replace("y", "_"))
    es = prover.add_instantiated_assumption(
        es_str,
        prover.ES,
        {
            "R": f"Ax[{ui_first_temp}]".replace("y", "_"),
            "Q": ui_second,
            "x": "y",
        },
    )

    return prover.qed()


def _prove_not_exists_not_implies_all(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4a


def _prove_exists_not_implies_not_all(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4b


def prove_not_all_iff_exists_not(
    variable: str, formula: Formula, print_as_proof_forms: bool = False
) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        variable: variable name for the quantifications in the formula to be
            proven.
        formula: statement to be universally quantified, and whose negation is
            to be existentially quantified, in the formula to be proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being created.

    Returns:
        A valid proof of the above formula via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4c
