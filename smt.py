import ast
import traceback
from enum import Enum

from z3 import *
from colorama import Fore, Style, init
from prompt_toolkit import prompt
from prompt_toolkit.completion import WordCompleter
import prompt_toolkit.output
from prompt_toolkit.history import InMemoryHistory

from sexpdata import loads, Symbol

from textual.app import App, ComposeResult
from textual.widgets import Tree
from textual.containers import Vertical
from textual import events
import sys

history = InMemoryHistory()
init()
init(autoreset=True)


class ProofObligation:
    def __init__(self, exp: z3.ExprRef, hypotheses: list, goal: str, axioms: z3.ExprRef, dict_prove: dict,
                 dict_names: dict,
                 scoped_vars: dict, proof,
                 origin: str, func_decls: dict, func_axioms: dict, recursive_funcs: dict, non_recursive_funcs: dict,
                 auxiliary_funcs: set):
        self.exp = exp  # Exp without not
        self.hyp = hypotheses
        self.goal = goal
        self.axioms = axioms
        self.dict_prove = dict_prove
        self.dict_names = dict_names
        self.scoped_vars = scoped_vars
        self.proof = proof
        self.origin = origin
        self.func_decls = func_decls
        self.func_axioms = func_axioms
        self.recursive_funcs = recursive_funcs
        self.non_recursive_funcs = non_recursive_funcs
        self.auxiliary_funcs = auxiliary_funcs

    def __repr__(self):
        return (f"Proof Obligation(\n"
                f"  hypotheses = [\n    " + "\n    ".join(self.hyp) + "\n  ],\n"
                                                                      f"  goal= {self.c}\n"
                                                                      f")")

    def pretty_print(self):
        print(Fore.YELLOW + "hypotheses:")
        for hyp in self.hyp:
            print(Fore.WHITE + "  ", str(hyp))
        print(Fore.YELLOW + "\ngoal:")
        print(Fore.WHITE + "  ", self.goal)
        print(Style.RESET_ALL)


class Proof:
    def __init__(self, kind: str):
        self.kind = kind

    def __repr__(self):
        # return f"{self.__class__.__name__}()"
        return f"{self.kind}()"


class AutomaticProof(Proof):
    def __init__(self):
        super().__init__("automatic")

    def print(self, indent=0):
        # pad = " " * indent
        # return f"{pad}automatic()"
        return ""


class AssertionProof(Proof):
    def __init__(self, expr, po1: ProofObligation = None, po2: ProofObligation = None):
        super().__init__("assertion")
        self.expr = expr
        self.po1 = po1
        self.po2 = po2

    def __repr__(self):
        po1_str = str(self.po1.proof) if self.po1 else "None"
        po2_str = str(self.po2.proof) if self.po2 else "None"
        return f"AssertionProof(expr={self.expr}, po1={po1_str}, po2={po2_str})"

    def print(self, indent=0):
        pad = " " * indent
        po1_str = self.po1.proof.print(indent + 2) if self.po1 else "None"
        po2_str = self.po2.proof.print(indent) if self.po2 else "None"

        if po1_str == "":
            return f"{pad}assert {pretty_print_expr_recursive(self.po1.dict_names, self.expr, self.po1.scoped_vars)}"f";\n{po2_str}"
        return f"{pad}assert {pretty_print_expr_recursive(self.po1.dict_names, self.expr, self.po1.scoped_vars)} by {{\n{po1_str}\n{pad}}}\n{po2_str}"


class CaseProof(Proof):
    def __init__(self, expr, po1: ProofObligation = None, po2: ProofObligation = None):
        super().__init__("case")
        self.expr = expr
        self.po1 = po1
        self.po2 = po2

    def __repr__(self):
        po1_str = str(self.po1) if self.po1 else "None"
        po2_str = str(self.po2) if self.po2 else "None"
        return f"CaseProof(expr={self.expr}, po1={po1_str}, po2={po2_str})"

    def print(self, indent=0):
        pad = " " * indent
        po1_str = self.po1.proof.print(indent + 2) if self.po1 else "None"
        po2_str = self.po2.proof.print(indent + 2) if self.po2 else "None"
        return f"{pad}if ({pretty_print_expr_recursive(self.po1.dict_names, self.expr, self.po1.scoped_vars)}) {{\n{po1_str}\n{pad}}} else {{\n{po2_str}\n{pad}}}"


class UnknownProof(Proof):
    def __init__(self):
        super().__init__("unknown")

    def print(self, indent=0):
        # pad = " " * indent
        # return f"{pad}unknown()"
        raise Exception("Trying to print UnknownProof.")


class AssumeProof(Proof):
    def __init__(self, expr, po1: ProofObligation, po2: ProofObligation):
        super().__init__("assume")
        self.expr = expr
        self.po1 = po1  # wf
        self.po2 = po2

    def __repr__(self):
        po1_str = str(self.po1.proof) if self.po1 else "None"
        return f"AssumeProof(expr={self.expr}, po1={po1_str})"

    def print(self, indent=0):
        pad = " " * indent
        po1_str = self.po1.proof.print(indent + 2) if self.po1 and self.po1.proof else ""
        if po1_str == "":
            return f"{pad}assume {pretty_print_expr_recursive(self.po1.dict_names, self.expr, self.po1.scoped_vars)}"";"
        return f"{pad}assume {pretty_print_expr_recursive(self.po1.dict_names, self.expr, self.po1.scoped_vars)}\n{pad} by {{\n{po1_str}\n{pad}}}"


class FuelType(Enum):
    EXPLICIT = "explicit"
    IMPLICIT = "implicit"
    NONE = "none"


class FunctionCategory(Enum):
    NON_RECURSIVE_NO_FUEL = "non_recursive_no_fuel"
    NON_RECURSIVE_EXPLICIT_FUEL = "non_recursive_explicit_fuel"
    RECURSIVE_EXPLICIT_FUEL = "recursive_explicit_fuel"
    RECURSIVE_IMPLICIT_FUEL = "recursive_implicit_fuel"


def extract_all_functions(expr):
    """
    Analyzes a Z3 expression and extracts information about functions.

    Returns:
        - recursive_funcs: Dict[str, Dict] - recursive functions with details
        - non_recursive_funcs: Dict[str, Dict] - non-recursive functions with details
        - auxiliary_funcs: Set[str] - system auxiliary functions
    """

    # LayerType = DeclareSort('LayerType')
    # IntSort = IntSort()

    # Collect all functions from the expression
    all_functions = set()
    layer_type_funcs = set()  # Functions with first arg T@LayerType
    start_fuel_funcs = set()  # StartFuel functions

    def collect_functions(e):
        """Recursively traverses the expression and collects functions."""
        if is_app(e):
            func_decl = e.decl()
            func_name = func_decl.name()
            all_functions.add(func_name)

            # Check if the first argument is of type LayerType
            if func_decl.arity() > 0:
                first_arg_sort = func_decl.domain(0)
                if "LayerType" in str(first_arg_sort):  # or LayerType == first_arg_sort
                    layer_type_funcs.add(func_name)

            # Check if it's a StartFuel function
            if func_name.startswith("StartFuel__"):
                base_func = func_name.replace("StartFuel_", "")
                base_func = base_func.replace("._default", ".__default")
                start_fuel_funcs.add(base_func)

            # Process arguments
            for child in e.children():
                collect_functions(child)
        elif is_quantifier(e):
            collect_functions(e.body())

    # Start collection
    collect_functions(expr)

    # Identify system auxiliary functions
    auxiliary_funcs = set()
    for func in all_functions:
        if (func == "ControlFlow" or
                func.startswith("$") or
                func.startswith("BaseFuel__") or
                func == "AsFuelBottom" or
                func.startswith("StartFuel__") or
                func.startswith("StartFuelAssert__") or
                func == "$LZ" or
                func == "$LS"):
            auxiliary_funcs.add(func)

    # Identify user functions
    user_funcs = all_functions - auxiliary_funcs

    # Classify user functions
    recursive_funcs = {}
    non_recursive_funcs = {}

    for func in user_funcs:
        has_layer_type = func in layer_type_funcs
        has_start_fuel = func in start_fuel_funcs

        if not has_layer_type:
            # Case I: Non-recursive without fuel
            non_recursive_funcs[func] = {
                "category": FunctionCategory.NON_RECURSIVE_NO_FUEL,
                "fuel_type": FuelType.NONE,
                "has_layer_type": False,
                "has_start_fuel": False
            }
        elif has_layer_type and has_start_fuel:
            # Case II: Can be recursive or non-recursive with explicit fuel
            # Assume recursive if it has StartFuel
            recursive_funcs[func] = {
                "category": FunctionCategory.RECURSIVE_EXPLICIT_FUEL,
                "fuel_type": FuelType.EXPLICIT,
                "has_layer_type": True,
                "has_start_fuel": True
            }
        elif has_layer_type and not has_start_fuel:
            # Case III: Recursive with implicit fuel
            recursive_funcs[func] = {
                "category": FunctionCategory.RECURSIVE_IMPLICIT_FUEL,
                "fuel_type": FuelType.IMPLICIT,
                "has_layer_type": True,
                "has_start_fuel": False
            }

    return recursive_funcs, non_recursive_funcs, auxiliary_funcs


def transform_expression_with_fuel(expr, recursive_funcs, non_recursive_funcs):
    """
    Transforms a Z3 expression by adding fuel parameters to recursive functions.

    Args:
        expr: Z3 expression to transform
        recursive_funcs: Dict of recursive functions with their details
        non_recursive_funcs: Dict of non-recursive functions with their details

    Returns:
        Transformed Z3 expression with fuel parameters added
    """

    # Get LayerType sort and create fuel expressions
    LayerType = DeclareSort('LayerType')
    LZ = Function('$LZ', LayerType)
    LS = Function('$LS', LayerType, LayerType)

    # Create $LS($LS($LZ())) for implicit fuel (2 levels of unrolling)
    implicit_fuel = LS(LS(LZ()))

    def transform_app(e):
        """Recursively transforms function applications."""
        if not is_app(e):
            if is_quantifier(e):
                # Transform quantifier body
                return substitute(e, [(e.body(), transform_app(e.body()))])
            return e

        func_decl = e.decl()
        func_name = func_decl.name()

        # Check if this is a user function that needs fuel
        if func_name in recursive_funcs:
            func_info = recursive_funcs[func_name]

            # Transform children first
            new_args = [transform_app(child) for child in e.children()]

            # Case II: Recursive with explicit fuel
            if func_info['category'] == FunctionCategory.RECURSIVE_EXPLICIT_FUEL:
                # Create StartFuelAssert function
                start_fuel_assert = Const(f"StartFuelAssert__{func_name}", LayerType)

                # Create new function with fuel parameter
                arg_sorts = [LayerType] + [func_decl.domain(i) for i in range(func_decl.arity())]
                new_func = Function(func_name, *arg_sorts, func_decl.range())

                # Apply with fuel as first argument
                return new_func(start_fuel_assert, *new_args)

            # Case III: Recursive with implicit fuel
            elif func_info['category'] == FunctionCategory.RECURSIVE_IMPLICIT_FUEL:
                # Create new function with fuel parameter
                arg_sorts = [LayerType] + [func_decl.domain(i) for i in range(func_decl.arity())]
                new_func = Function(func_name, *arg_sorts, func_decl.range())

                # Apply with implicit fuel $LS($LS($LZ()))
                return new_func(implicit_fuel, *new_args)

        elif func_name in non_recursive_funcs:
            func_info = non_recursive_funcs[func_name]

            # Transform children first
            new_args = [transform_app(child) for child in e.children()]

            # Case I: Non-recursive without fuel - no transformation needed
            if func_info['category'] == FunctionCategory.NON_RECURSIVE_NO_FUEL:
                if new_args != list(e.children()):
                    return func_decl(*new_args)
                return e

            # Non-recursive with explicit fuel (if exists)
            elif func_info['fuel_type'] == FuelType.EXPLICIT:
                start_fuel_assert = Const(f"StartFuelAssert__{func_name}", LayerType)
                arg_sorts = [LayerType] + [func_decl.domain(i) for i in range(func_decl.arity())]
                new_func = Function(func_name, *arg_sorts, func_decl.range())
                return new_func(start_fuel_assert, *new_args)

        # For other functions (system functions, etc.), just transform children
        new_args = [transform_app(child) for child in e.children()]
        if new_args != list(e.children()):
            return func_decl(*new_args)
        return e

    return transform_app(expr)


def extract_var_from_seqbuild(node, lit_value) -> str:
    """ Extracts a string variable from a Z3 Seq#Build model node.
     Recursively processes the sequence structure and decodes characters from $Box nodes."""

    if str(node.decl()) == lit_value:
        if len(node.children()) != 1:
            raise ValueError("Unexpected Lit_xxx structure")
        node = node.children()[0]

    def unfold_seqbuild(n):
        if str(n.decl()) == "Seq#Empty":
            return []

        if str(n.decl()) != "Seq#Build":
            raise ValueError(f"Unexpected node {n}")

        head, *tail = n.children()

        if str(head.decl()) == "Seq#Empty":
            return [decode_box(t) for t in tail]

        return unfold_seqbuild(head) + [decode_box(t) for t in tail]

    def decode_box(box_node):
        if not str(box_node.decl()).startswith("$Box"):
            raise ValueError(f"Unexpected node inside Seq#Build: {box_node}")
        if len(box_node.children()) != 1:
            raise ValueError("Box node does not contain exactly one child")

        char_expr = box_node.children()[0]
        if str(char_expr.decl()) != "char#FromInt":
            raise ValueError(f"Invalid Box content: {char_expr}")

        code = int(str(char_expr.children()[0]))
        return chr(code)

    chars = unfold_seqbuild(node)
    return "".join(chars)


def collect_variables(expr, var_counts=None) -> dict:
    """
        Recursively collects all variables from a Z3 expression and counts their occurrences.
        Returns a dictionary mapping variable names to their frequency, excluding boolean literals.
        """
    if var_counts is None:
        var_counts = {}

    try:
        if is_app(expr):
            if expr.decl().arity() == 0:
                var_name = str(expr.decl())

                if var_name.lower() not in ("true", "false"):

                    if var_name in var_counts:
                        var_counts[var_name] += 1
                    else:
                        var_counts[var_name] = 1

            for i in range(expr.num_args()):
                collect_variables(expr.arg(i), var_counts)

        return var_counts

    except Exception as e:
        print(f"Error when colecting variables: {e}")
        import traceback
        print(traceback.format_exc())
        return var_counts


def remove_Alloc(expr):
    """
        Recursively removes IsAlloc constraints from a Z3 expression by replacing them with True.
        """
    try:
        if is_app(expr):
            decl_name = expr.decl().name()

            if "IsAlloc" in decl_name:
                return BoolVal(True)

            if expr.num_args() > 0:
                new_args = [remove_Alloc(expr.arg(i)) for i in range(expr.num_args())]

                func = expr.decl()
                return func(*new_args)
            else:
                return expr
        else:
            return expr
    except Exception as e:
        print(f"Error when removing Alloc: {e}")
        import traceback
        print(traceback.format_exc())
        return expr

def pretty_print_expr_recursive(dict_names, expr, variables, indent=0, func_decls=None, recursive_funcs=None,
                                non_recursive_funcs=None, in_hypothesis=True) -> str:
    """
    Recursively converts a Z3 expression into a human-readable string with proper formatting and symbol replacement.
    Handles fuel parameters for recursive functions.
    Tracks hypothesis position to hide single-occurrence variable constraints.

    in_hypothesis: True if current expression is in hypothesis position
    """
    spaces = "  " * indent
    expr_str = str(expr)
    if func_decls is None:
        func_decls = {}
    if recursive_funcs is None:
        recursive_funcs = {}
    if non_recursive_funcs is None:
        non_recursive_funcs = {}
    try:
        if is_quantifier(expr):
            if expr.is_forall():
                body = expr.body()

                # Implies(And(Not(... == null), $Unbox...($Heap...[alloc])), $Heap@X[...] == $Heap@Y[...])
                if is_app(body) and body.decl().name() in ("=>", "Implies"):
                    implies_children = body.children()
                    if len(implies_children) >= 2:
                        antecedent = implies_children[0]
                        consequent = implies_children[1]

                        if is_app(antecedent) and antecedent.decl().name().lower() == "and":
                            and_children = antecedent.children()
                            has_null_check = False
                            has_unbox_heap = False

                            for and_child in and_children:
                                and_child_str = str(and_child)
                                if "== null" in and_child_str or "null ==" in and_child_str:
                                    has_null_check = True
                                if "$Unbox" in and_child_str and "$Heap" in and_child_str and "[alloc]" in and_child_str:
                                    has_unbox_heap = True

                            consequent_str = str(consequent)
                            has_heap_equality = "$Heap" in consequent_str and "==" in consequent_str

                            if has_null_check and has_unbox_heap and has_heap_equality:
                                return ""

        if is_app(expr):
            decl_name = expr.decl().name()
            children = expr.children()

            # Handle __protect - just unwrap it and show the protected value
            if decl_name == "__protect":
                if len(children) >= 2:
                    # Return the second argument (the actual value)
                    return pretty_print_expr_recursive(dict_names, children[1], variables, indent, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)
                elif len(children) == 1:
                    return pretty_print_expr_recursive(dict_names, children[0], variables, indent, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)

            # Handle List#Equal - convert to ==
            if "List#Equal" in decl_name:
                if len(children) == 2:
                    left = pretty_print_expr_recursive(dict_names, children[0], variables, indent, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)
                    right = pretty_print_expr_recursive(dict_names, children[1], variables, indent, func_decls,
                                                        recursive_funcs, non_recursive_funcs, in_hypothesis)
                    if left == "" or right == "":
                        return ""
                    return f"({left} == {right})"

            # Handle List.Cons
            if "List.Cons" in decl_name or decl_name == "#_module.List.Cons":
                if len(children) == 2:
                    head = pretty_print_expr_recursive(dict_names, children[0], variables, indent, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)
                    tail = pretty_print_expr_recursive(dict_names, children[1], variables, indent, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)
                    return f"Cons({head}, {tail})"

            if decl_name in ("==", "="):
                if len(children) == 2:
                    left_str = str(children[0])
                    right_str = str(children[1])

                    # Check if this matches the AsFuelBottom pattern
                    if "AsFuelBottom" in left_str and "BaseFuel__" in left_str and "BaseFuel__" in right_str:
                        if is_app(children[0]) and children[0].decl().name() == "AsFuelBottom":
                            inner = children[0].children()
                            if len(inner) > 0:
                                inner_str = str(inner[0])
                                if inner_str == right_str and "BaseFuel__" in inner_str:
                                    return ""

                    # Check if this is a constraint (= var expr) in hypothesis position
                    if in_hypothesis and is_app(children[0]) and children[0].decl().arity() == 0:
                        const_name = children[0].decl().name()
                        if const_name in variables and const_name.startswith('##'):
                            if variables[const_name] == 1:
                                return ""

            if "#IsAlloc" in decl_name:
                return ""

            if decl_name.endswith("#canCall"):
                func_decls[decl_name] = expr.decl()
                return ""

            if decl_name == "LitInt":
                if "module.__default." in str(expr.arg(0)):
                    return pretty_print_expr_recursive(dict_names, expr.arg(0), variables, indent + 1, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)
                return str(children[0])

            elif decl_name == "char#FromInt":
                if expr.num_args() > 0:
                    try:
                        val_int = int(str(expr.arg(0)))
                        return chr(val_int)
                    except ValueError:
                        return None
                return None

            # Handle $Unbox operations - remove the wrapper
            elif decl_name.startswith("$Unbox"):
                return pretty_print_expr_recursive(dict_names, expr.arg(0), variables, indent + 1, func_decls,
                                                   recursive_funcs, non_recursive_funcs, in_hypothesis)

            elif decl_name.startswith("$Box_"):
                return pretty_print_expr_recursive(dict_names, expr.arg(0), variables, indent + 1, func_decls,
                                                   recursive_funcs, non_recursive_funcs, in_hypothesis)

            elif decl_name.startswith("Lit_"):
                return pretty_print_expr_recursive(dict_names, expr.arg(0), variables, indent + 1, func_decls,
                                                   recursive_funcs, non_recursive_funcs, in_hypothesis)

            # Handle Seq#Length - display as |s|
            elif decl_name == "Seq#Length":
                if expr.num_args() > 0:
                    seq_expr = pretty_print_expr_recursive(dict_names, expr.arg(0), variables, indent, func_decls,
                                                           recursive_funcs, non_recursive_funcs, in_hypothesis)
                    return f"|{seq_expr}|"
                return "Seq#Length()"

            # Handle Seq#Index - display as array notation
            elif decl_name == "Seq#Index":
                if expr.num_args() >= 2:
                    seq_expr = pretty_print_expr_recursive(dict_names, expr.arg(0), variables, indent, func_decls,
                                                           recursive_funcs, non_recursive_funcs, in_hypothesis)
                    index_expr = pretty_print_expr_recursive(dict_names, expr.arg(1), variables, indent, func_decls,
                                                             recursive_funcs, non_recursive_funcs, in_hypothesis)
                    return f"{seq_expr}[{index_expr}]"
                return "Seq#Index()"

            elif decl_name == "Seq#Build":
                elements = [
                    pretty_print_expr_recursive(dict_names, expr.arg(i), variables, indent + 1, func_decls,
                                                recursive_funcs, non_recursive_funcs, in_hypothesis)
                    for i in range(expr.num_args())
                ]
                return "[" + ", ".join(str(e) if e is not None else "None" for e in elements) + "]"

            elif decl_name == "Seq#Empty":
                return "[]"

            elif decl_name in ("=>", "Implies"):
                if len(children) == 2:
                    # antecedent has inverted flag, consequent keeps the flag
                    antecedent = pretty_print_expr_recursive(dict_names, children[0], variables, indent + 1, func_decls,
                                                             recursive_funcs, non_recursive_funcs, not in_hypothesis)
                    consequent = pretty_print_expr_recursive(dict_names, children[1], variables, indent + 1, func_decls,
                                                             recursive_funcs, non_recursive_funcs, in_hypothesis)
                    if consequent == "":
                        return ""
                    if antecedent == "":
                        return f"({consequent})"
                    return f"({antecedent} →\n{spaces}  {consequent})"
                else:
                    return f"→({', '.join(pretty_print_expr_recursive(dict_names, c, variables, indent + 1, func_decls, recursive_funcs, non_recursive_funcs, in_hypothesis) for c in children)})"

            elif decl_name.lower() == "not":
                # Invert the flag when going through NOT
                child_result = pretty_print_expr_recursive(dict_names, children[0], variables, indent, func_decls,
                                                           recursive_funcs, non_recursive_funcs, not in_hypothesis)

                # Special case: if negating an equality, use != instead of ¬(... == ...)
                if is_app(children[0]) and children[0].decl().name() in ("==", "="):
                    child_children = children[0].children()
                    if len(child_children) == 2:
                        left = pretty_print_expr_recursive(dict_names, child_children[0], variables, indent, func_decls,
                                                           recursive_funcs, non_recursive_funcs, not in_hypothesis)
                        right = pretty_print_expr_recursive(dict_names, child_children[1], variables, indent,
                                                            func_decls,
                                                            recursive_funcs, non_recursive_funcs, not in_hypothesis)
                        if left != "" and right != "":
                            return f"({left} != {right})"

                return f"¬({child_result})"

            elif decl_name.lower() == "and":
                # Keep the flag for AND children
                child_strs = [
                    pretty_print_expr_recursive(dict_names, c, variables, indent + 1, func_decls, recursive_funcs,
                                                non_recursive_funcs, in_hypothesis) for c in children]
                child_strs = [s for s in child_strs if s != "" and s.casefold() != "true"]
                if len(child_strs) == 0:
                    return ""
                if len(child_strs) == 1:
                    return child_strs[0]
                if len(children) > 2:
                    separator = f"\n{spaces}  ∧ "
                    return f"({child_strs[0]}{separator}{separator.join(child_strs[1:])})"
                return f"({' ∧ '.join(child_strs)})"

            elif decl_name.lower() == "or":
                # Keep the flag for OR children
                child_strs = [
                    pretty_print_expr_recursive(dict_names, c, variables, indent + 1, func_decls, recursive_funcs,
                                                non_recursive_funcs, in_hypothesis) for c in children]
                child_strs = [s for s in child_strs if s != ""]
                if len(child_strs) == 0:
                    return ""
                if len(child_strs) == 1:
                    return child_strs[0]
                return f"({' ∨ '.join(child_strs)})"

            elif decl_name in ("<=", "<", "==", ">=", "+", "-", "=", ">"):
                if len(children) == 2:
                    left = pretty_print_expr_recursive(dict_names, children[0], variables, indent, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)
                    right = pretty_print_expr_recursive(dict_names, children[1], variables, indent, func_decls,
                                                        recursive_funcs, non_recursive_funcs, in_hypothesis)
                    symbol = decl_name
                    if symbol == "=":
                        symbol = "=="
                    if left == "" or right == "":
                        return ""
                    return f"({left} {symbol} {right})"

            elif decl_name == "Mul":
                func_decls[decl_name] = expr.decl()
                return f"({' * '.join(pretty_print_expr_recursive(dict_names, c, variables, indent, func_decls, recursive_funcs, non_recursive_funcs, in_hypothesis) for c in children)})"
            elif decl_name.casefold() == "mod":
                if len(children) == 2:
                    left = pretty_print_expr_recursive(dict_names, children[0], variables, indent, func_decls,
                                                       recursive_funcs, non_recursive_funcs, in_hypothesis)
                    right = pretty_print_expr_recursive(dict_names, children[1], variables, indent, func_decls,
                                                        recursive_funcs, non_recursive_funcs, in_hypothesis)
                    return f"({left} % {right})"
            elif decl_name.casefold() == "div":
                return f"({pretty_print_expr_recursive(dict_names, children[0], variables, indent, func_decls, recursive_funcs, non_recursive_funcs, in_hypothesis)} / {pretty_print_expr_recursive(dict_names, children[1], variables, indent, func_decls, recursive_funcs, non_recursive_funcs, in_hypothesis)})"
            elif decl_name == "Int":
                return expr_str
            elif decl_name.startswith("$") and "$Unbox" not in decl_name:
                return ""
            elif decl_name.startswith("ControlFlow") or "lambda" in decl_name:
                return ""
            else:
                if expr.decl().arity() == 0:  # is_constant
                    const_name = expr.decl().name()
                    # Remove the old check - now only done in (= var expr) context
                    if const_name.lower() == "false":
                        return "false"
                    if const_name.lower() == "true":
                        return "true"

                    # Handle List.Nil constant
                    if "List.Nil" in const_name or const_name.startswith("#_module.List.Nil"):
                        return "Nil"

                    if const_name in dict_names:
                        return dict_names[const_name]


                # Check if this is a user function with fuel (cases II, III)
                func_name = decl_name
                has_fuel = func_name in recursive_funcs or (
                        func_name in non_recursive_funcs and non_recursive_funcs[func_name][
                    'fuel_type'].value != 'none')

                if has_fuel and len(children) > 0:
                    first_arg = children[0]
                    first_arg_str = str(first_arg)

                    is_start_fuel_assert = "StartFuelAssert__" in first_arg_str
                    is_implicit_fuel = is_implicit_fuel_pattern(first_arg)

                    if is_start_fuel_assert or is_implicit_fuel:
                        children = children[1:]
                    else:
                        raise Exception(
                            f"Unhandled fuel case for function '{func_name}': first argument is '{first_arg_str}' which is neither StartFuelAssert nor implicit fuel pattern ($LS($LS($LZ())))")

                func_decls[decl_name] = expr.decl()

                # Skip type parameters that look like Append(_module._default.AppendNil$T, ...)
                filtered_children = []
                for child in children:
                    child_str = str(child)
                    # Skip type parameter arguments (e.g., _module._default.AppendNil$T)
                    if not ("$T" in child_str and "_module._default." in child_str and len(child_str) < 50):
                        filtered_children.append(child)

                child_strs = [
                    pretty_print_expr_recursive(dict_names, child, variables, indent, func_decls, recursive_funcs,
                                                non_recursive_funcs, in_hypothesis) for child in filtered_children]
                child_strs = [s for s in child_strs if s != ""]

                display_name = decl_name
                if display_name.startswith("_module.__default."):
                    display_name = display_name.replace("_module.__default.", "")

                return display_name + f"({', '.join(child_strs)})" if child_strs else display_name
        else:
            return str(expr)
    except:
        print(traceback.format_exc())

def is_implicit_fuel_pattern(expr):
    """
    Checks if an expression matches the implicit fuel pattern: $LS($LS($LZ()))
    """
    if not is_app(expr):
        return False

    # Check if outermost is $LS
    if expr.decl().name() != "$LS":
        return False

    # Check if it has one child
    if expr.num_args() != 1:
        return False

    inner1 = expr.arg(0)

    # Check if inner is also $LS
    if not is_app(inner1) or inner1.decl().name() != "$LS":
        return False

    if inner1.num_args() != 1:
        return False

    inner2 = inner1.arg(0)

    # Check if innermost is $LZ
    if not is_app(inner2) or inner2.decl().name() != "$LZ":
        return False

    # Check if $LZ has no arguments
    if inner2.num_args() != 0:
        return False

    return True


# func_decls = {}

def extract_implications_recursive(dict_names, expr, variables, recursive_funcs, non_recursive_funcs):
    """
        Extracts hypotheses and goal from a chain of implications in a Z3 expression.
        """
    hypotheses = []
    if expr.decl().name().lower() == "not":
        expr = expr.children()[0]

    hypotheses = []
    # global func_decls
    func_decls = {}

    def recurse(e):
        if is_app(e) and e.decl().name() in ("=>", "Implies") and e.num_args() == 2:
            hyp_str = pretty_print_expr_recursive(dict_names, e.arg(0), variables, 0, func_decls, recursive_funcs,
                                                  non_recursive_funcs)
            if hyp_str != "":
                hypotheses.append(hyp_str)
            return recurse(e.arg(1))
        else:
            return pretty_print_expr_recursive(dict_names, e, variables, 0, func_decls, recursive_funcs,
                                               non_recursive_funcs, False)

    goal = recurse(expr)
    return hypotheses, goal, func_decls


def create_function_call_with_fuel(func_name, args, recursive_funcs, non_recursive_funcs, func_decls):
    """
    Creates a Z3 function call with fuel parameters if needed.

    Args:
        func_name: Name of the function to create
        args: List of Z3 expressions (already transformed arguments)
        recursive_funcs: Dict of recursive functions with their details
        non_recursive_funcs: Dict of non-recursive functions with their details
        func_decls: Dict of original function declarations

    Returns:
        Z3 expression: Complete function call with fuel if needed
    """

    # Get LayerType sort and create fuel expressions
    LayerType = DeclareSort('T@LayerType')
    LZ = Function('$LZ', LayerType)
    LS = Function('$LS', LayerType, LayerType)

    # Create $LS($LS($LZ())) for implicit fuel (2 levels of unrolling)
    implicit_fuel = LS(LS(LZ()))

    # Get original function declaration
    if func_name not in func_decls:
        raise ValueError(f"Function {func_name} not found in func_decls")

    original_func = func_decls[func_name]

    # Case 1: RECURSIVE WITH EXPLICIT FUEL
    if func_name in recursive_funcs:
        func_info = recursive_funcs[func_name]

        if func_info['category'] == FunctionCategory.RECURSIVE_EXPLICIT_FUEL:

            expected_args = original_func.arity() - 1  # exclude fuel parameter
            if len(args) != expected_args:
                raise ValueError(
                    f"Function {func_name} (RECURSIVE_EXPLICIT_FUEL) expects {expected_args} arguments (without fuel), "
                    f"got {len(args)}. Original arity: {original_func.arity()}"
                )

            func_name = func_name.replace(".__", "._")
            start_fuel_assert = Const(f"StartFuelAssert_{func_name}", LayerType)

            new_args = [start_fuel_assert] + args

            return original_func(*new_args)

        # Case 2: RECURSIVE WITH IMPLICIT FUEL
        elif func_info['category'] == FunctionCategory.RECURSIVE_IMPLICIT_FUEL:

            expected_args = original_func.arity() - 1  # exclude fuel parameter
            if len(args) != expected_args:
                raise ValueError(
                    f"Function {func_name} (RECURSIVE_IMPLICIT_FUEL) expects {expected_args} arguments (without fuel), "
                    f"got {len(args)}. Original arity: {original_func.arity()}"
                )

            new_args = [implicit_fuel] + args

            return original_func(*new_args)

    # Case 3: NON-RECURSIVE WITHOUT FUEL
    elif func_name in non_recursive_funcs:
        func_info = non_recursive_funcs[func_name]

        if func_info['category'] == FunctionCategory.NON_RECURSIVE_NO_FUEL:
            expected_args = original_func.arity()
            if len(args) != expected_args:
                raise ValueError(
                    f"Function {func_name} (NON_RECURSIVE_NO_FUEL) expects {expected_args} arguments, "
                    f"got {len(args)}. Original arity: {original_func.arity()}"
                )
            return original_func(*args)

        # Case 4: NON-RECURSIVE WITH EXPLICIT FUEL
        elif func_info['fuel_type'] == FuelType.EXPLICIT:

            expected_args = original_func.arity() - 1  # exclude fuel parameter
            if len(args) != expected_args:
                raise ValueError(
                    f"Function {func_name} (NON_RECURSIVE with EXPLICIT fuel) expects {expected_args} arguments (without fuel), "
                    f"got {len(args)}. Original arity: {original_func.arity()}"
                )

            func_name = func_name.replace("__", "_")
            start_fuel_assert = Const(f"StartFuelAssert_{func_name}", LayerType)

            new_args = [start_fuel_assert] + args

            return original_func(*new_args)

    expected_args = original_func.arity()
    if len(args) != expected_args:
        raise ValueError(
            f"Function {func_name} (UNCATEGORIZED) expects {expected_args} arguments, "
            f"got {len(args)}. Original arity: {original_func.arity()}\n"
            f"Function is not in recursive_funcs or non_recursive_funcs - assuming no fuel."
        )
    return original_func(*args)


def ast_to_z3(current_proofOb, node):
    """
        Converts a Python AST node to its equivalent Z3 expression using the provided variable dictionary.
        """
    if isinstance(node, ast.Call):
        func_name = None
        if isinstance(node.func, ast.Name):
            func_name = node.func.id

        if func_name is None:
            raise NotImplementedError(f"Unsupported function call format")

        args = [ast_to_z3(current_proofOb, arg) for arg in node.args]

        full_func_name = "_module.__default." + func_name

        return create_function_call_with_fuel(
            full_func_name,
            args,
            current_proofOb.recursive_funcs,
            current_proofOb.non_recursive_funcs,
            current_proofOb.func_decls
        )

        # if func_name in current_proofOb.func_decls:
        #     # func_decl = Function(func_name)
        #     return current_proofOb.func_decls[func_name](*args)

    if isinstance(node, ast.BinOp):
        left = ast_to_z3(current_proofOb, node.left)
        right = ast_to_z3(current_proofOb, node.right)
        if isinstance(node.op, ast.Add):
            return left + right
        elif isinstance(node.op, ast.Sub):
            return left - right
        elif isinstance(node.op, ast.Mult):
            return current_proofOb.func_decls["Mul"](left, right)
        elif isinstance(node.op, ast.Div):
            return left / right
        elif isinstance(node.op, ast.Mod):
            return left % right
        else:
            raise NotImplementedError(f"Unsupported binary operator: {node.op}")

    elif isinstance(node, ast.Compare):
        left = ast_to_z3(current_proofOb, node.left)
        right = ast_to_z3(current_proofOb, node.comparators[0])
        if isinstance(node.ops[0], ast.Eq):
            result = right == left
            return result
        elif isinstance(node.ops[0], ast.NotEq):
            return left != right
        elif isinstance(node.ops[0], ast.Lt):
            return left < right
        elif isinstance(node.ops[0], ast.LtE):
            return left <= right
        elif isinstance(node.ops[0], ast.Gt):
            return left > right
        elif isinstance(node.ops[0], ast.GtE):
            return left >= right
        else:
            raise NotImplementedError(f"Unsupported comparison operator: {node.ops[0]}")

    elif isinstance(node, ast.BoolOp):
        values = [ast_to_z3(current_proofOb, v) for v in node.values]
        if isinstance(node.op, ast.And):
            return z3.And(*values)
        elif isinstance(node.op, ast.Or):
            return z3.Or(*values)
        else:
            raise NotImplementedError(f"Unsupported boolean operator: {node.op}")

    elif isinstance(node, ast.UnaryOp):
        operand = ast_to_z3(current_proofOb, node.operand)
        if isinstance(node.op, ast.Not):
            return z3.Not(operand)
        elif isinstance(node.op, ast.USub):  # -x
            return -operand
        elif isinstance(node.op, ast.UAdd):  # +x
            return operand
        else:
            raise NotImplementedError(f"Unsupported unary operator: {node.op}")

    elif isinstance(node, ast.IfExp):
        cond = ast_to_z3(current_proofOb, node.test)
        body = ast_to_z3(current_proofOb, node.body)
        orelse = ast_to_z3(current_proofOb, node.orelse)
        return z3.If(cond, body, orelse)

    elif isinstance(node, ast.Name):
        if node.id.lower() == "true":
            return z3.BoolVal(True)
        elif node.id.lower() == "false":
            return z3.BoolVal(False)
        elif node.id in current_proofOb.dict_prove:
            return current_proofOb.dict_prove[node.id]
        else:
            raise ValueError(f"Variable '{node.id}' not defined in dict_prove")

    elif isinstance(node, ast.Constant):
        if isinstance(node.value, int):
            return z3.IntVal(node.value)
        elif isinstance(node.value, float):
            return z3.RealVal(node.value)
        elif isinstance(node.value, bool):
            return z3.BoolVal(node.value)
        else:
            raise NotImplementedError(f"Unsupported constant: {node.value}")

    elif isinstance(node, ast.Subscript):
        value = ast_to_z3(current_proofOb, node.value)
        index = ast_to_z3(current_proofOb, node.slice)
        return value[index]

    else:
        raise NotImplementedError(f"Unsupported AST node type: {type(node).__name__}")


def create_assert_proof_obligations(proofOb: ProofObligation, assert_expr, wf_expr, wf_prime_expr):
    """
        Splits a proof obligation into two: one proving the assertion holds, and one assuming it to prove the goal.
        """
    expr = proofOb.exp
    # wf_expr = the well-f of the assert_expr
    antecedents = []
    while is_app(expr) and expr.decl().name() in ("=>", "Implies") and expr.num_args() == 2:
        antecedent = expr.arg(0)  # Γ
        antecedents.append(antecedent)
        consequent = expr.arg(1)  # ψ
        expr = consequent

    # we prove wf_prime_expr
    exp3 = wf_prime_expr

    for a in reversed(antecedents):
        exp3 = Implies(a, exp3)

    hyp3 = proofOb.hyp
    c3 = pretty_print_expr_recursive(proofOb.dict_names, wf_prime_expr, proofOb.scoped_vars, 0, proofOb.func_decls,
                                     proofOb.recursive_funcs, proofOb.non_recursive_funcs)
    po3 = ProofObligation(exp3, hyp3, c3, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                          UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                          proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    # 1. Γ → ¬instr wf is added as a hypo
    exp1 = assert_expr
    if wf_expr is not None:
        exp1 = Implies(wf_expr, exp1)

    for a in reversed(antecedents):
        exp1 = Implies(a, exp1)

    hyp1 = proofOb.hyp
    c1 = pretty_print_expr_recursive(proofOb.dict_names, assert_expr, proofOb.scoped_vars, 0, proofOb.func_decls,
                                     proofOb.recursive_funcs, proofOb.non_recursive_funcs)
    po1 = ProofObligation(exp1, hyp1, c1, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                          UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                          proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    # 2. (Γ ∧ instr) → ψ
    exp2 = Implies(assert_expr, consequent)
    if wf_expr is not None:
        exp2 = Implies(wf_expr, exp2)

    for a in reversed(antecedents):
        exp2 = Implies(a, exp2)

    hyp2 = proofOb.hyp[:] + [
        pretty_print_expr_recursive(proofOb.dict_names, assert_expr, proofOb.scoped_vars, 0, proofOb.func_decls,
                                    proofOb.recursive_funcs, proofOb.non_recursive_funcs)]
    c2 = proofOb.goal
    po2 = ProofObligation(exp2, hyp2, c2, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                          UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                          proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    return [po3, po1, po2]


def create_case_proof_obligations(proofOb: ProofObligation, cond, wf_cond, wf_prime_expr):
    """
        Splits a proof obligation into two cases: one assuming the condition is true, and one assuming it is false.
        """
    expr = proofOb.exp

    antecedents = []
    while is_app(expr) and expr.decl().name() in ("=>", "Implies") and expr.num_args() == 2:
        antecedent = expr.arg(0)  # Γ
        antecedents.append(antecedent)
        consequent = expr.arg(1)  # ψ
        expr = consequent

    exp3 = wf_prime_expr

    for a in reversed(antecedents):
        exp3 = Implies(a, exp3)

    hyp3 = proofOb.hyp
    c3 = pretty_print_expr_recursive(proofOb.dict_names, wf_prime_expr, proofOb.scoped_vars, 0, proofOb.func_decls,
                                     proofOb.recursive_funcs, proofOb.non_recursive_funcs)
    po3 = ProofObligation(exp3, hyp3, c3, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                          UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                          proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    # 1: Γ ∧ cond → ψ
    exp1 = Implies(cond, consequent)

    if wf_cond is not None:
        exp1 = Implies(wf_cond, exp1)

    for a in reversed(antecedents):
        exp1 = Implies(a, exp1)
    hyp1 = proofOb.hyp[:] + [
        pretty_print_expr_recursive(proofOb.dict_names, cond, proofOb.scoped_vars, 0, proofOb.func_decls,
                                    proofOb.recursive_funcs, proofOb.non_recursive_funcs)]
    # print(pretty_print_expr_recursive(proofOb.dict_names, cond))
    c1 = proofOb.goal
    po1 = ProofObligation(exp1, hyp1, c1, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                          UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                          proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    # 2: Γ ∧ ¬cond → ψ
    not_cond = Not(cond)
    exp2 = Implies(not_cond, consequent)
    if wf_cond is not None:
        exp2 = Implies(wf_cond, exp2)

    for a in reversed(antecedents):
        exp2 = Implies(a, exp2)
    hyp2 = proofOb.hyp[:] + [
        pretty_print_expr_recursive(proofOb.dict_names, not_cond, proofOb.scoped_vars, 0, proofOb.func_decls,
                                    proofOb.recursive_funcs, proofOb.non_recursive_funcs)]
    c2 = proofOb.goal
    po2 = ProofObligation(exp2, hyp2, c2, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                          UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                          proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    return [po3, po1, po2]


def create_assume_proof_obligations(proofOb: ProofObligation, assume_expr, wf_cond, wf_prime_expr):
    """
        Creates a new proof obligation by adding the assumption to the hypotheses and proving the original goal.
        """
    expr = proofOb.exp

    antecedents = []
    while is_app(expr) and expr.decl().name() in ("=>", "Implies") and expr.num_args() == 2:
        antecedent = expr.arg(0)  # Γ
        antecedents.append(antecedent)
        consequent = expr.arg(1)  # ψ
        expr = consequent

    exp3 = wf_prime_expr

    for a in reversed(antecedents):
        exp3 = Implies(a, exp3)

    hyp3 = proofOb.hyp
    c3 = pretty_print_expr_recursive(proofOb.dict_names, wf_prime_expr, proofOb.scoped_vars, 0, proofOb.func_decls,
                                     proofOb.recursive_funcs, proofOb.non_recursive_funcs)
    po3 = ProofObligation(exp3, hyp3, c3, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                          UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                          proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    # 1. (Γ ∧ instr) → ψ
    exp = Implies(assume_expr, consequent)

    if wf_cond is not None:
        exp = Implies(wf_cond, exp)

    for a in reversed(antecedents):
        exp = Implies(a, exp)

    hyp = proofOb.hyp[:] + [
        pretty_print_expr_recursive(proofOb.dict_names, assume_expr, proofOb.scoped_vars, 0, proofOb.func_decls,
                                    proofOb.recursive_funcs, proofOb.non_recursive_funcs)]
    c = proofOb.goal

    po = ProofObligation(exp, hyp, c, proofOb.axioms, proofOb.dict_prove, proofOb.dict_names, proofOb.scoped_vars,
                         UnknownProof, "new", proofOb.func_decls, proofOb.func_axioms, proofOb.recursive_funcs,
                         proofOb.non_recursive_funcs, proofOb.auxiliary_funcs)

    return [po3, po]


def print_proof_obligations(proof_obligations):
    """
        Displays all unproven proof obligations.
        """
    filtered_pos = [po for po in proof_obligations if po.proof == UnknownProof]
    print(Fore.GREEN + f"\n{len(filtered_pos)} goal(s) remaining\n")

    if not proof_obligations:
        return

    current_po = filtered_pos[0]
    print(Fore.BLUE + "current goal:")
    print(Fore.YELLOW + "hypotheses")
    for hyp in current_po.hyp:
        print("  ", hyp)

    print(Fore.YELLOW + "goal")
    print("  ", current_po.goal)
    print()

    count = 2
    for i, po in enumerate(filtered_pos):
        if po is current_po:
            continue
        print(Fore.CYAN + f"Goal {count}:" + Style.RESET_ALL, po.goal)
        count += 1
    print()


def removeProtectCanCall(expr: ExprRef) -> ExprRef:
    """
        Recursively removes Dafny protect#canCall predicates from a Z3 expression by replacing them with True.
        """
    if not z3.is_app(expr):
        return expr
    if expr.decl().name().endswith(".__default.__protectToProve#canCall"):
        return BoolVal(True)
    if expr.decl().name().endswith(".__default.__protect#canCall"):
        return BoolVal(True)
    if expr.decl().name().endswith(".__default.__protectScope#canCall"):
        return BoolVal(True)

    # If the expression has children (args), recursively apply the same logic
    if expr.num_args() > 0:
        new_args = [removeProtectCanCall(a) for a in expr.children()]
        return expr.decl()(*new_args)

    return expr


def process_lit_value(expr: ExprRef) -> str:
    """
    Recursively search for a Lit_ function of type Tseq -> Tseq.
    Returns the literal value if found, otherwise None.
    e.g. (Lit_29744 (|Seq#Build| |Seq#Empty| ($Box_27519 (|char#FromInt| 120))))) -> 29744
    """
    Tseq = DeclareSort('T@Seq')
    if is_app(expr):
        decl_name = expr.decl().name()

        # Case 1: direct Lit_ function
        if decl_name.startswith("Lit_"):
            if isinstance(expr.decl(), FuncDeclRef) and expr.decl().arity() == 1:
                if expr.decl().domain(0) == Tseq and expr.decl().range() == Tseq:
                    return decl_name
                else:
                    raise Exception("Different Lit value for T@Seq -> T@Seq function.")

        # Case 2: recurse into children
        for child in expr.children():
            lit = process_lit_value(child)
            if lit is not None:
                return lit

    # No literal found
    return None


def buildScopedVarsList(expr, scoped_vars=None):
    """
       Recursively extracts scoped variables from __protectToProve expressions in a Z3 expression tree.
       """
    if scoped_vars is None:
        scoped_vars = []

    decl_name = expr.decl().name() if is_app(expr) else str(expr)

    # --- Case: $Unbox_? (protectToProve …)
    if decl_name.startswith("$Unbox_"):
        inner = expr.arg(0)
        inner_decl = inner.decl().name() if is_app(inner) else str(inner)

        if inner_decl.endswith(".__default.__protectToProve"):
            # [TBool, reveal..., ($Box_x var), name_expr, scope_expr]
            scope_expr = inner.arg(4) if inner.num_args() > 4 else None

            # Extract variables from scope
            if scope_expr is not None:
                new_scoped_vars = extract_scoped_variables(scope_expr)
                scoped_vars.extend(new_scoped_vars)

            # Recursively process the boxed expression
            box_expr = inner.arg(2)
            unboxed_expr = box_expr.arg(0)
            buildScopedVarsList(unboxed_expr, scoped_vars)

    # Recursively process all children
    if is_app(expr):
        for i in range(expr.num_args()):
            buildScopedVarsList(expr.arg(i), scoped_vars)

    return scoped_vars


def buildDictionaries(expr, scoped_vars=None, dict_prove=None, dict_names=None, lit_value=None):
    """
        Recursively builds mappings between variable names and Z3 expressions from __protect annotations.
        """
    if scoped_vars is None:
        scoped_vars = []
    if dict_prove is None:
        dict_prove = {}
    if dict_names is None:
        dict_names = {}
    if lit_value is None:
        lit_value = ""

    decl_name = expr.decl().name() if is_app(expr) else str(expr)

    # --- Case: $Unbox_? (protect/protectToProve …)
    if decl_name.startswith("$Unbox_"):
        inner = expr.arg(0)
        inner_decl = inner.decl().name() if is_app(inner) else str(inner)

        if inner_decl.endswith(".__default.__protect"):
            # [TInt, reveal..., ($Box_x var), name_expr]
            box_var, name_expr = inner.arg(2), inner.arg(3)
            unboxed_var = box_var.arg(0)  # |n#0|

            name = extract_var_from_seqbuild(name_expr, lit_value)

            # Update dict_names
            if str(unboxed_var) in dict_names:
                if dict_names[str(unboxed_var)] != name:
                    raise Exception(
                        "Building dict_names: name {0} already set to {1} (cannot set to {2})".format(
                            str(unboxed_var),
                            dict_names[str(unboxed_var)],
                            name))
            dict_names[str(unboxed_var)] = name

            # Update dict_prove
            if name in dict_prove:
                if not dict_prove[name].eq(unboxed_var):
                    # Check if unboxed_var exists in scoped_vars
                    found_in_scope = None
                    for scoped_var in scoped_vars:
                        if scoped_var.eq(unboxed_var):
                            found_in_scope = scoped_var
                            break

                    if found_in_scope is not None:
                        # Use the scoped variable instead
                        dict_prove[name] = found_in_scope
            else:
                dict_prove[name] = unboxed_var

        if inner_decl.endswith(".__default.__protectToProve"):
            # [TBool, reveal..., ($Box_x var), name_expr, scope_expr]
            box_expr = inner.arg(2)
            unboxed_expr = box_expr.arg(0)

            # Recursively process with the same scoped_vars
            buildDictionaries(unboxed_expr, scoped_vars, dict_prove, dict_names, lit_value)

    # Recursively process all children
    if is_app(expr):
        for i in range(expr.num_args()):
            buildDictionaries(expr.arg(i), scoped_vars, dict_prove, dict_names, lit_value)

    return dict_prove, dict_names


def removeProtectToProve(expr):
    """
        Recursively removes __protect and __protectToProve wrappers from a Z3 expression, extracting the underlying variables.
        """
    decl_name = expr.decl().name() if is_app(expr) else str(expr)

    # --- Case: $Unbox_? (protect/protectToProve …)
    if decl_name.startswith("$Unbox_"):
        inner = expr.arg(0)
        inner_decl = inner.decl().name() if is_app(inner) else str(inner)

        if inner_decl.endswith(".__default.__protect"):
            # [TInt, reveal..., ($Box_x var), name_expr]
            box_var = inner.arg(2)
            unboxed_var = box_var.arg(0)  # |n#0|
            return unboxed_var

        if inner_decl.endswith(".__default.__protectToProve"):
            # [TBool, reveal..., ($Box_x var), name_expr, scope_expr]
            box_expr = inner.arg(2)
            unboxed_expr = box_expr.arg(0)
            return removeProtectToProve(unboxed_expr)

    # Recursively process all children
    if is_app(expr):
        new_args = [removeProtectToProve(expr.arg(i)) for i in range(expr.num_args())]
        return expr.decl()(*new_args)

    return expr


def extract_scoped_variables(scope_expr):
    """
    Extract variables from scope expression.
    Traverses Seq#Build structures and extracts variables from __protectScope calls.
    Returns list of variable expressions.
    """
    if scope_expr is None:
        return []

    variables = []

    def traverse_seq(expr):
        if not is_app(expr):
            return

        decl_name = expr.decl().name()

        # Check if it's a Seq#Build
        if decl_name == "Seq#Build":
            # Seq#Build has 2 args: the sequence so far, and the new element
            if expr.num_args() >= 2:
                # Recurse on the first arg (the sequence)
                traverse_seq(expr.arg(0))

                # Process the second arg (the new element)
                elem = expr.arg(1)
                if is_app(elem):
                    elem_decl = elem.decl().name()

                    # Check if it's a $Box_* containing __protectScope
                    if elem_decl.startswith("$Box_"):
                        inner = elem.arg(0)
                        if is_app(inner):
                            inner_decl = inner.decl().name()

                            # Check if it's __protectScope
                            if inner_decl.endswith(".__default.__protectScope"):
                                # [TInt, reveal..., ($Box_x var)]
                                if inner.num_args() >= 3:
                                    box_var = inner.arg(2)
                                    if is_app(box_var) and box_var.decl().name().startswith("$Box_"):
                                        var_expr = box_var.arg(0)
                                        variables.append(var_expr)

    traverse_seq(scope_expr)
    return variables


def remove_protect(ast: ExprRef):
    """
        Removes all __protect annotations from a Z3 expression and extracts variable mappings and scoped variables.
        """

    lit_value = process_lit_value(ast)

    expr = removeProtectCanCall(ast)

    variables = buildScopedVarsList(expr)
    dict_prove = {}
    dict_names = {}
    dict_prove, dict_names = buildDictionaries(expr, variables, dict_prove, dict_names, lit_value)

    clean_expr = removeProtectToProve(expr)

    return clean_expr, dict_prove, dict_names


def process_proof_obligations(input_text):
    """
      Parses SMT-LIB input text and extracts axioms and proof obligation expressions separated by push/pop commands.
      """

    proof_obligations = input_text.split("(pop 1)")

    proofs_str = []

    for p in proof_obligations:
        if "(push 1)" in p:
            axioms, expr = p.split("(push 1)")
            proofs_str.append((axioms.strip(), expr.strip()))

    return proofs_str


def print_proof_obligation(po: ProofObligation, indent: int = 0):
    pad = " " * indent
    result = f"{pad}Goal: {po.goal}\n"
    # result += f"{pad}Expr: {po.exp}\n"
    result += f"{pad}Proof:\n"
    result += po.proof.print(indent + 2)
    print(result)


def wf(expr, func_decls, recursive_funcs, non_recursive_funcs):
    """
    Compute well-formedness conditions for a Z3 expression.
    Returns a conjunction of constraints that must hold for the expression to be well-formed.

    For functions with fuel parameters, the fuel parameter is skipped when creating canCall predicates.

    Examples:
    - Division: x / 2 generates constraint: 2 != 0
    - Function call (no fuel): inc(x / 2) generates: inc#canCall(x) && 2 != 0
    - Function call (with fuel): even($LS($LS($LZ())), x) generates: even#canCall(x) && (x >= 0)
    - Nested: inc(x / 2) == funcall(10) generates: inc#canCall(x) && 2 != 0 && funcall#canCall(10)
    """
    conditions = []

    def has_fuel_parameter(func_name):
        """
        Determines if a function expects a fuel parameter.

        Returns:
            bool: True if function has fuel parameter, False otherwise
        """
        # Check recursive functions (all have fuel)
        if func_name in recursive_funcs:
            return True

        # Check non-recursive functions with explicit fuel
        if func_name in non_recursive_funcs:
            func_info = non_recursive_funcs[func_name]
            return func_info['fuel_type'] != FuelType.NONE

        # If not categorized, assume no fuel
        return False

    def walk(e):
        """Recursively walk the expression tree and collect WF conditions."""

        # Base case: constants and variables are always well-formed
        if is_const(e) or is_var(e):
            return

        # Handle function applications
        if is_app(e):
            decl = e.decl()
            kind = decl.kind()

            # Division - check divisor != 0
            if kind == Z3_OP_DIV or kind == Z3_OP_IDIV:
                divisor = e.arg(1)
                conditions.append(divisor != 0)
                # Recursively check operands
                for i in range(e.num_args()):
                    walk(e.arg(i))

            # Modulo - check divisor != 0
            elif kind == Z3_OP_MOD or kind == Z3_OP_REM:
                divisor = e.arg(1)
                conditions.append(divisor != 0)
                for i in range(e.num_args()):
                    walk(e.arg(i))

            # Uninterpreted function call - add canCall predicate
            elif kind == Z3_OP_UNINTERPRETED:
                func_name = decl.name()

                # Get all arguments from the function call
                all_args = [e.arg(i) for i in range(e.num_args())]

                # Determine if function has fuel and extract actual arguments
                has_fuel = has_fuel_parameter(func_name)

                if has_fuel:
                    # Skip first argument (fuel parameter)
                    if len(all_args) > 0:
                        canCall_args = all_args[1:]  # Skip fuel, keep rest
                        print(f"  WF: {func_name} has fuel, skipping first arg")
                    else:
                        # Function has no arguments besides fuel?
                        canCall_args = []
                        print(f"  WF: {func_name} has fuel but no arguments")
                else:
                    # No fuel - use all arguments
                    canCall_args = all_args

                # Create canCall predicate with the correct arguments
                func_name_can_call = f"{func_name}#canCall"

                if func_name_can_call in func_decls:
                    try:
                        func_can_call_decl = func_decls[func_name_can_call]

                        # Verify argument count matches
                        expected_args = func_can_call_decl.arity()
                        if len(canCall_args) != expected_args:
                            print(
                                f"   WF Warning: {func_name}#canCall expects {expected_args} args, got {len(canCall_args)}")
                            print(f"     Has fuel: {has_fuel}, Total args: {len(all_args)}")

                        # Create the canCall predicate
                        func_can_call = func_can_call_decl(*canCall_args)
                        conditions.append(func_can_call)

                    except Exception as ex:
                        print(f"     WF Error: Cannot create {func_name_can_call}: {ex}")
                        print(f"     Expected arity: {func_can_call_decl.arity()}")
                        print(f"     Provided args: {len(canCall_args)}")
                        print(f"     Has fuel: {has_fuel}")

                # Recursively check arguments (all arguments, including fuel if present)
                for arg in all_args:
                    walk(arg)

            # Other operators - recursively check arguments
            else:
                for i in range(e.num_args()):
                    walk(e.arg(i))

        # Handle quantifiers
        elif is_quantifier(e):
            walk(e.body())

    # Start the recursive walk
    walk(expr)

    # Return conjunction of all conditions (True if no conditions)
    if not conditions:
        return BoolVal(True)
    elif len(conditions) == 1:
        return conditions[0]
    else:
        return And(conditions)


def safe_prompt():
    """
    Provides an interactive command prompt with auto-completion, falling back to standard input if unavailable.
    """

    COMMANDS = ["assert", "case", "assume", "check", ":undo", ":help", ":quit", ":focus", ":set-timeout"]
    try:
        try:
            prompt_toolkit.output.create_output()
        except:
            raise

        completer = WordCompleter(COMMANDS, ignore_case=True)

        return prompt(
            'Enter a tactic (e.g., assert <expression>, :help, :quit): ',
            completer=completer, history=history
        )

    except Exception as e:
        print(Fore.YELLOW + f"[Fallback] Switching to standard input due to: {type(e).__name__}" + Style.RESET_ALL)
        return input(Fore.CYAN + 'Enter a tactic (e.g., assert <expression>, :help, :quit): ' + Style.RESET_ALL)


def configure_solver_options():
    """
        Configures Z3 solver options for model-based quantifier instantiation, arithmetic solving, and timeout limits.
        """
    set_option("smt.mbqi", False)
    set_option("model.compact", False)
    set_option("model.v2", True)
    set_option("pp.bv_literals", False)
    set_option("smt.arith.solver", 2)

    solver = Solver()
    solver.set("mbqi", False)
    solver.set("arith.solver", 2)
    solver.set("timeout", timeout_miliseconds)
    solver.set("rlimit", rlimit)
    return solver


def try_prove_current_goal(current_proofOb, proof_obligations):
    """
    Attempts to automatically prove the current proof obligation using Z3 solver with configured options.
    """
    solver = configure_solver_options()
    solver.push()
    solver.add(current_proofOb.axioms)
    solver.add(Not(current_proofOb.exp))

    status = solver.check()

    if status == unsat:
        print(Fore.GREEN + "Congrats, current goal proved." + Style.RESET_ALL)
        proof_obligations[0].proof = AutomaticProof()
        proof_obligations.pop(0)
        return True
    else:
        print(Fore.MAGENTA + "Solver check status: " + Style.RESET_ALL + str(status))
        print(Fore.RED + "Current goal not yet proved." + Style.RESET_ALL)
        return False


def print_help():
    print(Fore.CYAN + "\n=== HELP ===" + Style.RESET_ALL)
    print(Fore.YELLOW + "Available commands:" + Style.RESET_ALL)
    print(" assert <expression>   - add a new assertion to the current goal")
    print(" case (<expression>)   - add a case split to the current goal")
    print(" assume (<expression>) - add an assumption to the current goal")
    print(" check (<expression>)  - assert and verify an expression in the current goal")
    print(" :undo                 - revert last change to goals")
    print(" :quit                 - exit the interactive session")
    print(" :help                 - display this help message")
    print(" :focus <n>            - set the current goal to the goal at index n (1-based index)")
    print(" :set-timeout <n>      - set solver timeout to n milliseconds")
    print(" :set-rlimit <n>       - set solver resource limit to n")
    print(" :show                 - show the goals that must be proved")
    print(Fore.YELLOW + "\nExamples:" + Style.RESET_ALL)
    print("  assert x > 0")
    print("  assert f(n) == 10")
    print(Fore.CYAN + "================\n" + Style.RESET_ALL)


def handle_undo(history, proof_obligations):
    if history:
        proof_obligations = history.pop()
        print("Undo performed. Goals restored.")
    else:
        print("Nothing to undo.")
    return proof_obligations


def handle_focus(instr, proof_obligations):
    try:
        n = int(instr.split()[1])
        filtered_pos = [po for po in proof_obligations if po.proof == UnknownProof]
        if 1 <= n <= len(filtered_pos):
            goal_to_focus = filtered_pos[n - 1]
            proof_obligations.remove(goal_to_focus)
            proof_obligations.insert(0, goal_to_focus)
            print(f"Focused on goal {n}.")
        else:
            print(f"Invalid goal index: {n}")
    except (IndexError, ValueError):
        print("Usage: :focus <n>")


def handle_set_timeout(instr):
    global timeout_miliseconds
    try:
        n = int(instr.split()[1])
        timeout_miliseconds = n
        # solver.set("timeout", timeout_seconds)
        print(f"Timeout set to {n} miliseconds.")
    except (IndexError, ValueError):
        print("Usage: :set-timeout <n>")


def handle_set_rlimit(instr):
    global rlimit
    try:
        n = int(instr.split()[1])
        rlimit = n
        print(f"rlimit set to {n}.")
    except (IndexError, ValueError):
        print("Usage: :set-rlimit <n>")


def get_func_name_from_canCallExp(wf_expr):
    """
    Extracts the function name from a WF expression containing canCall.

    Given:
        wf_expr = And(_module.__default.inc#canCall(x#0@@24/2), 2 != 0)

    Returns:
        The function name: _module.__default.inc

    Args:
        wf_expr: the well-formedness expression containing canCall
    """
    if wf_expr is None:
        return None

    def extract_function_name(expr):
        """Recursively search for canCall predicate and extract the function name."""
        if is_app(expr):
            # Check if this is a canCall predicate
            decl_name = expr.decl().name()
            if "#canCall" in decl_name:
                # Example: "_module.__default.inc#canCall"
                func_name = decl_name.replace("#canCall", "")
                return func_name

            # Recursively search in arguments
            for i in range(expr.num_args()):
                result = extract_function_name(expr.arg(i))
                if result is not None:
                    return result

        return None

    func_name = extract_function_name(wf_expr)

    if func_name is None:
        return None
    else:
        return func_name


def get_func_requires(func_axioms, func_name):
    """
    Safely retrieves the requirements (axioms) for a given function name
    from the provided func_axioms dictionary, with all necessary checks.
    """

    if func_name not in func_axioms:
        print(f"[Warning] Function '{func_name}' not found in func_axioms.")
        return None

    func_requires = func_axioms[func_name]

    return func_requires


def compute_wf_prime(wf_formula, current_proofOb):
    func_name = get_func_name_from_canCallExp(wf_formula)

    func_axioms = current_proofOb.func_axioms

    wf_prime_formula = wf_formula
    if func_name is not None:
        func_requires = get_func_requires(func_axioms, func_name)
        wf_prime_formula = construct_wf_prime(wf_formula, func_requires, current_proofOb.recursive_funcs,
                                              current_proofOb.non_recursive_funcs)

    return wf_prime_formula


def handle_assert(stmt, current_proofOb, proof_obligations, history):
    exp = stmt.test
    formula = ast_to_z3(current_proofOb, exp)
    # print(f"Formula {formula}.")
    # return
    wf_formula = wf(formula, current_proofOb.func_decls, current_proofOb.recursive_funcs,
                    current_proofOb.non_recursive_funcs)
    wf_prime_formula = compute_wf_prime(wf_formula, current_proofOb)

    history.append(copy.deepcopy(proof_obligations))

    # formula_with_fuel = transform_expression_with_fuel(formula)

    new_proof_obligations = create_assert_proof_obligations(current_proofOb, formula, wf_formula, wf_prime_formula)
    proof_obligations[0].proof = AssertionProof(formula, new_proof_obligations[1],
                                                new_proof_obligations[2])
    proof_obligations.append(proof_obligations.pop(0))
    proof_obligations[0:0] = new_proof_obligations


def handle_case(stmt, current_proofOb, proof_obligations, history):
    cond_ast = stmt.value.args[0]
    cond_formula = ast_to_z3(current_proofOb, cond_ast)
    wf_formula = wf(cond_formula, current_proofOb.func_decls, current_proofOb.recursive_funcs,
                    current_proofOb.non_recursive_funcs)
    history.append(copy.deepcopy(proof_obligations))
    wf_prime_formula = compute_wf_prime(wf_formula, current_proofOb)

    new_proof_obligations = create_case_proof_obligations(current_proofOb, cond_formula, wf_formula, wf_prime_formula)
    proof_obligations[0].proof = CaseProof(cond_formula, new_proof_obligations[1],
                                           new_proof_obligations[2])
    proof_obligations.append(proof_obligations.pop(0))
    proof_obligations[0:0] = new_proof_obligations


def handle_assume(stmt, current_proofOb, proof_obligations, history):
    exp = stmt.value.args[0]
    formula = ast_to_z3(current_proofOb, exp)
    # print("Assume:", formula)
    wf_formula = wf(formula, current_proofOb.func_decls, current_proofOb.recursive_funcs,
                    current_proofOb.non_recursive_funcs)

    wf_prime_formula = compute_wf_prime(wf_formula, current_proofOb)

    history.append(copy.deepcopy(proof_obligations))
    new_proof_obligation = create_assume_proof_obligations(current_proofOb, formula, wf_formula, wf_prime_formula)
    proof_obligations[0].proof = AssumeProof(formula, new_proof_obligation[1], new_proof_obligation[2])

    proof_obligations.append(proof_obligations.pop(0))
    proof_obligations[0:0] = new_proof_obligation


def handle_check(stmt, current_proofOb):
    exp = stmt.value.args[0]
    phi = ast_to_z3(current_proofOb, exp)

    solver = configure_solver_options()
    for h in current_proofOb.hyp:
        solver.add(h)

    solver.push()
    solver.add(Not(phi))
    result = solver.check()
    solver.pop()

    if result == unsat:
        print(Fore.GREEN + f"Yes, can prove {ast.unparse(exp)} from the current set of hypotheses." + Style.RESET_ALL)
    else:
        print(Fore.RED + f"No, cannot prove {ast.unparse(exp)} from the current set of hypotheses." + Style.RESET_ALL)


def extract_wf_conditions(axioms, func_decls, recursive_funcs, non_recursive_funcs):
    """
    Extracts well-formedness conditions (requires) for functions from axioms.

    For each function in func_decls, searches through axioms for:
    - Functions WITHOUT fuel: ForAll([x0, x1, ...], Implies(F, function#canCall(x0, x1, ...)))
    - Functions WITH fuel: ForAll([ly:T@LayerType, x0, x1, ...], Implies(F, function#canCall(x0, x1, ...)))

    Returns a dictionary {function_name: F}

    Args:
        axioms: list of Z3 axioms
        func_decls: dict of function declarations
        recursive_funcs: dict of recursive functions with their details
        non_recursive_funcs: dict of non-recursive functions with their details

    Returns:
        dict: {function_name: wf_condition}
    """

    def has_fuel_parameter(func_name):
        """
        Determines if a function expects a fuel parameter.

        Returns:
            bool: True if function has fuel parameter, False otherwise
        """
        # Check recursive functions
        if func_name in recursive_funcs:
            # All recursive functions have fuel (either explicit or implicit)
            return True

        # Check non-recursive functions
        if func_name in non_recursive_funcs:
            func_info = non_recursive_funcs[func_name]
            # Non-recursive can have explicit fuel or no fuel
            return func_info['fuel_type'] != FuelType.NONE

        # If not categorized, assume no fuel
        return False

    def verify_forall_cancall(axiom, func_name, expects_fuel):
        """
        Verify that axiom has the structure:
        - WITHOUT fuel: ForAll([x0, x1, ...], Implies(F, func#canCall(x0, x1, ...)))
        - WITH fuel: ForAll([ly:T@LayerType, x0, x1, ...], Implies(F, func#canCall(x0, x1, ...)))

        where vars match between quantifier and canCall (excluding fuel parameter ly)

        Returns:
            (is_valid, antecedent) if valid, (False, None) otherwise
        """
        # Check if it's a ForAll quantifier
        if not (is_quantifier(axiom) and axiom.is_forall()):
            return False, None

        num_vars = axiom.num_vars()
        if num_vars == 0:
            return False, None

        # If function expects fuel, verify first variable is T@LayerType
        if expects_fuel:
            if num_vars < 2:  # Need at least ly + one parameter
                return False, None

            # Get the sort (type) of the first quantified variable
            first_var_sort = axiom.var_sort(0)
            first_var_sort_name = str(first_var_sort)

            # Check if first variable is of type T@LayerType (or LayerType, T@Layer, etc.)
            if "LayerType" not in first_var_sort_name and "Layer" not in first_var_sort_name:
                return False, None

            # Optional: strict check for exact name
            # if first_var_sort_name != "T@LayerType":
            #     return False, None

        body = axiom.body()

        # Check if body is an Implies
        if not (is_app(body) and body.decl().name() in ("=>", "Implies")):
            return False, None

        if body.num_args() != 2:
            return False, None

        antecedent = body.arg(0)  # F (the condition we want)
        consequent = body.arg(1)  # should be function#canCall(vars)

        if not is_app(consequent):
            return False, None

        consequent_name = consequent.decl().name()

        # Check if consequent is the canCall function for func_name
        if "#canCall" not in consequent_name or func_name not in consequent_name:
            return False, None

        # Determine expected number of canCall arguments based on fuel
        if expects_fuel:
            # WITH fuel: ForAll([ly, x0, x1, ...], ..., canCall(x0, x1, ...))
            # canCall should have num_vars - 1 arguments (excluding ly)
            expected_canCall_args = num_vars - 1
            var_offset = 1  # Skip first variable (ly)
        else:
            # WITHOUT fuel: ForAll([x0, x1, ...], ..., canCall(x0, x1, ...))
            # canCall should have num_vars arguments
            expected_canCall_args = num_vars
            var_offset = 0

        # Check if number of canCall arguments matches expectation
        if consequent.num_args() != expected_canCall_args:
            return False, None

        # Verify that canCall arguments are the correct variables
        # For WITH fuel: should be Var(0), Var(1), ..., Var(num_vars-2)
        #                (corresponding to x0, x1, ... in ForAll([ly, x0, x1, ...]))
        # For WITHOUT fuel: should be Var(0), Var(1), ..., Var(num_vars-1)
        #                   (corresponding to x0, x1, ... in ForAll([x0, x1, ...]))

        for i in range(expected_canCall_args):
            canCall_arg = consequent.arg(i)

            if not is_var(canCall_arg):
                return False, None

            # Z3 uses reverse indexing for de Bruijn indices
            # The i-th argument of canCall should correspond to Var(num_vars - 1 - (i + var_offset))
            expected_var_index = num_vars - 1 - (i + var_offset)

            if get_var_index(canCall_arg) != expected_var_index:
                return False, None

        return True, antecedent

    wf_conditions = {}

    for func_name in func_decls:
        # Determine if this function expects fuel
        expects_fuel = has_fuel_parameter(func_name)

        print(f"\nSearching for axiom for {func_name} (expects_fuel={expects_fuel})...")

        for axiom in axioms:
            is_valid, antecedent = verify_forall_cancall(axiom, func_name, expects_fuel)

            if is_valid:
                print(f"  Found valid ForAll with canCall for {func_name}")
                if expects_fuel:
                    first_var_sort = axiom.var_sort(0)
                    print(f"  First variable type: {first_var_sort}")
                wf_conditions[func_name] = antecedent
                break
        else:
            # Optional: debug why no matching axiom was found
            print(f"  No matching axiom found for {func_name}")
            for axiom in axioms:
                if is_quantifier(axiom) and axiom.is_forall():
                    body = axiom.body()
                    if is_app(body) and body.decl().name() in ("=>", "Implies"):
                        consequent = body.arg(1)
                        if is_app(consequent) and func_name in str(consequent):
                            print(f"  Found axiom mentioning {func_name} but structure doesn't match expected pattern")
                            print(f"    Axiom quantifier vars: {axiom.num_vars()}")
                            print(f"    Expected fuel: {expects_fuel}")
                            if expects_fuel and axiom.num_vars() > 0:
                                first_var_sort = axiom.var_sort(0)
                                print(f"    First variable type: {first_var_sort}")
                            if is_app(consequent):
                                print(f"    canCall args: {consequent.num_args()}")

    return wf_conditions


def create_requires_with_new_args(requires_expr, new_args):
    """
    Create a new requires expression with new_args as arguments.

    Args:
        requires_expr: original requires expression (e.g., inc#requires(x#0@@24/2))
        new_args: the new args of requires_expr

    Returns:
        New expression: inc#requires(new_arg)
    """
    if not is_app(requires_expr):
        print("Warning: requires_expr is not an application")
        return requires_expr

    if "#requires" not in requires_expr.decl().name():
        print("Warning: requires_expr does not contain #requires")
        return requires_expr
    try:
        # Get the function declaration
        func_decl = requires_expr.decl()

        new_expr = func_decl(*new_args)

        print(f"  Original: {requires_expr}")
        print(f"  With new arg: {new_expr}")

        return new_expr
    except Exception as ex:
        error_msg = (
            f"\n ERROR creating expression for {requires_expr.sexpr()}\n"
            f"   Exception: {ex}\n"
            f"   Original: {requires_expr}\n"
            f"   Args: {new_args}\n"
        )
        print(error_msg)
        raise


def construct_wf_prime(wf_expr, wf_condition, recursive_funcs, non_recursive_funcs):
    """
    Constructs WF'(E) from WF(E) by replacing the canCall predicate with the requires condition.

    Given:
        WF(E) = And(_module.__default.inc#canCall(x#0@@24/2), 2 != 0)
        F = _module.__default.inc#requires(x#0@@24/2)

    Returns:
        WF'(E) = And(F, 2 != 0)

    For functions with fuel:
        - Implicit fuel: inc#requires($LS($LS($LZ())), x, y)
        - Explicit fuel: inc#requires(StartFuelAssert_inc, x, y)

    Args:
        wf_expr: the well-formedness expression WF(E)
        wf_condition: the requires condition F extracted from axioms
        recursive_funcs: dict of recursive functions with their details
        non_recursive_funcs: dict of non-recursive functions with their details

    Returns:
        the modified expression WF'(E)
    """
    if wf_expr is None or wf_condition is None:
        return wf_expr

    # Get LayerType sort and create fuel expressions
    LayerType = DeclareSort('T@LayerType')
    LZ = Function('$LZ', LayerType)
    LS = Function('$LS', LayerType, LayerType)

    # Create $LS($LS($LZ())) for implicit fuel (2 levels of unrolling)
    implicit_fuel = LS(LS(LZ()))

    def extract_function_name_from_canCall(canCall_name):
        """
        Extract function name from canCall predicate.
        Example: '_module.__default.inc#canCall' -> 'inc'
        Returns: (full_name, short_name)
        """
        if "#canCall" in canCall_name:
            full_name = canCall_name.replace("#canCall", "")
            # Extract short name (after last dot)
            if "." in full_name:
                short_name = full_name.split(".")[-1]
            else:
                short_name = full_name
            return full_name, short_name
        return None, None

    def has_fuel_parameter(func_name):
        """
        Determines if a function expects a fuel parameter and its type.

        Returns:
            (has_fuel, fuel_type):
                - (False, None) if no fuel
                - (True, FunctionCategory.RECURSIVE_IMPLICIT_FUEL) if implicit fuel
                - (True, FunctionCategory.RECURSIVE_EXPLICIT_FUEL) if explicit fuel
        """
        # Check recursive functions
        if func_name in recursive_funcs:
            func_info = recursive_funcs[func_name]
            return True, func_info['category']

        # Check non-recursive functions with fuel
        if func_name in non_recursive_funcs:
            func_info = non_recursive_funcs[func_name]
            if func_info['fuel_type'] == FuelType.EXPLICIT:
                return True, FunctionCategory.NON_RECURSIVE_EXPLICIT_FUEL
            else:
                return False, None

        # If not categorized, assume no fuel
        return False, None

    def contains_canCall(expr):
        """Check if expression contains #canCall predicate."""
        if is_app(expr):
            if "#canCall" in expr.decl().name():
                return True
            for i in range(expr.num_args()):
                if contains_canCall(expr.arg(i)):
                    return True
        return False

    if not contains_canCall(wf_expr):
        return wf_expr

    def replace_canCall(expr, replacement):
        """Recursively replace canCall predicates with the replacement expression."""
        if is_app(expr):
            # If this is a canCall predicate, replace it
            if "#canCall" in expr.decl().name():
                canCall_name = expr.decl().name()
                full_func_name, short_func_name = extract_function_name_from_canCall(canCall_name)

                if full_func_name is None:
                    return expr

                # Get canCall arguments (the actual function parameters)
                canCall_args = [expr.arg(i) for i in range(expr.num_args())]

                # Check if function has fuel and what type
                has_fuel, fuel_category = has_fuel_parameter(full_func_name)

                if has_fuel:
                    # Determine fuel parameter based on category
                    if fuel_category == FunctionCategory.RECURSIVE_IMPLICIT_FUEL:
                        # Case 1: Implicit fuel - use $LS($LS($LZ()))
                        fuel_param = implicit_fuel
                        print(f"  Using implicit fuel for {short_func_name}")

                    elif fuel_category in (FunctionCategory.RECURSIVE_EXPLICIT_FUEL,
                                           FunctionCategory.NON_RECURSIVE_EXPLICIT_FUEL):
                        # Case 2: Explicit fuel - use StartFuelAssert_funcname
                        full_func_name = full_func_name.replace(".__", "._")
                        fuel_param = Const(f"StartFuelAssert_{full_func_name}", LayerType)
                        print(f"  Using explicit fuel for {full_func_name}")

                    else:
                        # Shouldn't happen, but handle gracefully
                        fuel_param = implicit_fuel
                        print(f"   Unknown fuel category for {short_func_name}, using implicit fuel")

                    # Create requires expression with fuel parameter first
                    # requires(fuel, arg1, arg2, ...)
                    new_args = [fuel_param] + canCall_args
                else:
                    # Case 3: No fuel - just use the original arguments
                    new_args = canCall_args
                    print(f"  No fuel for {short_func_name}")

                # Replace with requires condition using new arguments
                wf_condition_with_args = create_requires_with_new_args(replacement, new_args)

                return wf_condition_with_args

            # If this is an And/Or/other operation, recurse on arguments
            if expr.num_args() > 0:
                new_args = [replace_canCall(expr.arg(i), replacement) for i in range(expr.num_args())]

                # Reconstruct the expression with new arguments
                if expr.decl().name() == "and":
                    if len(new_args) == 1:
                        return new_args[0]
                    result = new_args[0]
                    for arg in new_args[1:]:
                        result = And(result, arg)
                    return result

        return expr

    return replace_canCall(wf_expr, wf_condition)


def handle_wf(stmt, current_proofOb):
    """
        Tactic that displays the well-formedness condition for an expression.
        """

    ast = stmt.value.args[0]
    formula = ast_to_z3(current_proofOb, ast)
    wf_formula = wf(formula, current_proofOb.func_decls, current_proofOb.recursive_funcs,
                    current_proofOb.non_recursive_funcs)
    # wf_cond = wf(expr)
    print(f"Expression: {formula}")
    print(f"WF Condition: {wf_formula}")
    print(f"Simplified: {simplify(wf_formula)}")
    wf_prime_formula = compute_wf_prime(wf_formula, current_proofOb)
    print(f"WF' Condition: {wf_prime_formula}")
    # return wf_formula


def parse_and_execute_instruction(instr, current_proofOb, proof_obligations, history):
    try:
        code_tree = ast.parse("false = False\ntrue = True\n" + instr, mode="exec")
        stmt = code_tree.body[2]

        if isinstance(stmt, ast.Assert):
            handle_assert(stmt, current_proofOb, proof_obligations, history)

        elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
            func_id = getattr(stmt.value.func, "id", "")

            if func_id == "case":
                handle_case(stmt, current_proofOb, proof_obligations, history)

            elif func_id == "assume":
                handle_assume(stmt, current_proofOb, proof_obligations, history)

            elif func_id == "check":
                handle_check(stmt, current_proofOb)
            elif func_id == "wf":
                handle_wf(stmt, current_proofOb)
    except IndexError as e:
        pass
        # print(Fore.RED + f"List index out of range: {e}" + Style.RESET_ALL)
    except Exception as e:
        print(Fore.RED + f"Invalid instruction: {e}" + Style.RESET_ALL)
        print(traceback.format_exc())


def read_file_content(file_path):
    with open(file_path, 'r', encoding='utf-8') as f:
        return f.read()


def parse_smt_axioms_and_expressions(proof_str):
    smt_axioms = parse_smt2_string(proof_str[0])
    smt_expressions = parse_smt2_string(proof_str[0] + '\n' + proof_str[1])

    expr = smt_expressions[len(smt_axioms)]
    axioms = smt_expressions[:len(smt_axioms)]

    return axioms, expr


def process_protect_to_prove(expr):
    recursive_funcs, non_recursive_funcs, auxiliary_funcs = extract_all_functions(expr)
    expr, dict_prove, dict_names = remove_protect(expr)
    expr_without_alloc = remove_Alloc(expr)
    variables = collect_variables(expr_without_alloc)
    h, c, func_decls = extract_implications_recursive(dict_names, expr, variables, recursive_funcs, non_recursive_funcs)

    if expr.decl().name().lower() == "not":
        # result = pretty_print_expr_recursive(dict_names, expr.children()[0])
        expr = expr.children()[0]
    else:
        raise ValueError("Error, not expected!")

    return expr, dict_prove, dict_names, variables, h, c, func_decls, recursive_funcs, non_recursive_funcs, auxiliary_funcs


def create_proof_obligation_from_string(proof_str):
    axioms, expr = parse_smt_axioms_and_expressions(proof_str)
    expr_str = expr.sexpr()
    # print("Proof obligation: {0}.".format(expr_str))
    if "protectToProve" in expr_str:
        expr, dict_prove, dict_names, scoped_vars, h, c, func_decls, recursive_funcs, non_recursive_funcs, auxiliary_funcs = process_protect_to_prove(
            expr)  # , final_result
        func_axioms = extract_wf_conditions(axioms, func_decls, recursive_funcs, non_recursive_funcs)
        return ProofObligation(expr, h, c, axioms, dict_prove, dict_names, scoped_vars, UnknownProof, "file",
                               func_decls, func_axioms, recursive_funcs, non_recursive_funcs, auxiliary_funcs)
    return None


def load_proof_obligations_from_file(file_path):
    content = read_file_content(file_path)
    proofs_str = process_proof_obligations(content)

    proof_obligations = []
    print("Identified {0} proof obligations in the SMT-LIB file.".format(len(proofs_str)))
    for proof_str in proofs_str:
        proof_obligation = create_proof_obligation_from_string(proof_str)
        if proof_obligation is not None:
            proof_obligations.append(proof_obligation)

    return proof_obligations


timeout_miliseconds = 1000
rlimit = 1000000
last_command = None


def contains_function(expr, func_name):
    try:
        if is_app(expr):
            decl_name = expr.decl().name()
            func_name_d = "_module.__default." + func_name
            # print(decl_name)
            if decl_name == func_name or decl_name == func_name_d:
                return True

            found = False
            for i, child in enumerate(expr.children()):
                if contains_function(child, func_name):
                    found = True
            return found

        elif is_quantifier(expr):
            return contains_function(expr.body(), func_name)

        return False
    except:
        return False


def handle_search(current_proofOb, instr):
    func_name = instr.split()[1]
    axioms = current_proofOb.axioms

    print(f"Searching for function: {func_name}")
    print(f"Total axioms to check: {len(axioms)}")
    print("-" * 80)

    found_axioms = []
    for i, axiom in enumerate(axioms):
        if contains_function(axiom, func_name):
            found_axioms.append(axiom)
            print(f"\n[Axiom {i + 1}]")
            print(axiom)
            print("-" * 80)

    print(f"\nFound {len(found_axioms)} axioms containing '{func_name}'")


def to_python_tree(obj):
    """Convert sexpdata parsed object into nested Python structure."""
    # sexpdata.loads produces Python lists and sexpdata.Symbol or strings/numbers
    if isinstance(obj, list):
        return [to_python_tree(x) for x in obj]
    if isinstance(obj, Symbol):
        return str(obj)  # convert symbol to string
    return obj


def pretty_label(node):
    if isinstance(node, list):
        return f"list ({len(node)})"
    return repr(node)


class SExpExplorer(App):
    CSS = """
    Screen { align: center middle; }
    """

    def __init__(self, data, **kwargs):
        super().__init__(**kwargs)
        self.data = data

    def compose(self) -> ComposeResult:
        yield Vertical(Tree("S-Expression"))

    async def on_mount(self):
        tree = self.query_one(Tree)
        tree.show_root = True
        tree.root.label = "root"
        self.build_tree(tree.root, self.data)
        tree.root.expand()  # start expanded

        # instructions
        self.set_focus(tree)

    def build_tree(self, node, data):
        """Recursively add children to textual Tree node."""
        if isinstance(data, list):
            for i, child in enumerate(data):
                label = pretty_label(child)
                child_node = node.add(label, data=child)
                # Add placeholder children for lists so node is expandable
                if isinstance(child, list):
                    # recursively populate
                    self.build_tree(child_node, child)
        else:
            # leaf: show value
            node.add_leaf(pretty_label(data))

    async def on_key(self, event: events.Key) -> None:
        tree = self.query_one(Tree)
        if event.key == "q":
            await self.action_quit()
        # Textual's Tree widget already handles arrow keys + Enter for expand/collapse.
        # We don't need to implement folding keys manually.


def initialize_ipm(file_path):
    """
    Initializes the IPM for a given file.
    Returns (proof_obligations, initial_state) or None if error.

    This function does all necessary setup but does NOT enter the interactive loop.
    """
    try:
        proof_obligations = load_proof_obligations_from_file(file_path)

        if proof_obligations is None:
            print("There are no proof obligations annotated with {ipm} in this file.")
            return None

        print(f"Have {len(proof_obligations)} proof obligations for the IPM.")

        initial_state = {
            'proof_obligations': proof_obligations,
            'history': [],
            'quit': False,
            'last_command': None
        }

        return initial_state

    except Exception as e:
        print(f"Error during initialization: {e}")
        print(traceback.format_exc())
        return None


# start_ipm sa mai ia un argument: functia care "citeste" comenzile de la tastatura

class X:
    def __init__(self, s):
        self.command = s

def safe_prompt_command():
    str = safe_prompt()
    return X(str)

def start_ipm(file_path, *commands):
    start_ipm_with_command(file_path, safe_prompt_command, *commands)


def start_ipm_with_command(file_path, get_next_command, *commands):
    try:

        initial_state = initialize_ipm(file_path)

        if initial_state is None:
            return None

        proof_obligations = initial_state['proof_obligations']
        history = initial_state['history']
        quit = initial_state['quit']
        last_command = initial_state['last_command']

        global timeout_seconds

        if commands:
            if commands[0] == "--explore":
                my_proof_obligations = [po for po in proof_obligations if po.proof == UnknownProof]
                if len(my_proof_obligations) == 0:
                    print("No proof obligations to explore.")
                    sys.exit(1)
                my_proof_obligation = my_proof_obligations[0]
                parsed = loads(my_proof_obligation.exp.sexpr())
                py_tree = to_python_tree(parsed)
                SExpExplorer(py_tree).run()
            elif commands[0] == "--print-all":
                print("\nAll goals from smt2 file.")
                for po in proof_obligations:
                    po.pretty_print()
                return proof_obligations
            else:
                print("Unrecognized command {0}".format(commands[0]))
                sys.exit(1)

        while not quit and any(po.proof is UnknownProof for po in proof_obligations):

            current_proofOb = next(po for po in proof_obligations if po.proof is UnknownProof)
            if last_command != "check" and last_command != "help" and last_command != "set-timeout" and last_command != "set-rlimit" and last_command != "search":

                print_proof_obligations(proof_obligations)
                if try_prove_current_goal(current_proofOb, proof_obligations):
                    continue

                instr = get_next_command().command  # safe_prompt()
            else:
                instr = get_next_command().command  # safe_prompt()

            if instr.lower() == ":quit":
                quit = True
                break

            elif instr.lower() == ":help":
                print_help()
                last_command = "help"
                continue

            elif instr.lower() == ":undo":
                proof_obligations = handle_undo(history, proof_obligations)
                last_command = "undo"
                continue

            elif instr.lower().startswith(":focus "):
                handle_focus(instr, proof_obligations)
                last_command = "focus"
                continue

            elif instr.lower().startswith(":set-timeout "):
                # solver = Solver()
                handle_set_timeout(instr)
                last_command = "set-timeout"
                continue

            elif instr.lower().startswith(":set-rlimit "):
                handle_set_rlimit(instr)
                last_command = "set-rlimit"
                continue

            elif instr.lower().startswith(":retry"):
                # handle_retry(instr)
                current_proofOb.proof = UnknownProof
                last_command = "retry"
                continue

            elif instr.lower().startswith(":search "):
                handle_search(current_proofOb, instr)
                last_command = "search"
                continue

            elif instr.lower().startswith(":show"):
                last_command = "show"
                continue

            parse_and_execute_instruction(instr, current_proofOb, proof_obligations, history)
            last_command = "check" if "check" in instr else None

        if not quit:
            for po in proof_obligations:
                if po.origin == "file":
                    print_proof_obligation(po)
        return proof_obligations
    except Exception as e:
        print(traceback.format_exc())
        print(f"Error while processing file: {e}")
        return None


if __name__ == "__main__":
    # check if the user provided a file path
    if len(sys.argv) < 2:
        print("Usage: python smt.py <file_path>")
    else:
        # call the function with the first command line argument
        if len(sys.argv) == 3:
            if sys.argv[2] == "--print-all":
                start_ipm(sys.argv[1], *sys.argv[2:])
            else:
                print(f"Processing {sys.argv[2]}... --print-all expected.")
        else:
            start_ipm(sys.argv[1])

        # test_with_file('C:\\Users\\Roxana\\Dynafny\\lemma1protect.smt2')

# assert (j + 1) * k <= l * k;
# assert (i + 1) * m <= q * m;


# _module.__default.protect |n#0| (Lit_23378 (|Seq#Build| |Seq#Empty| ($Box_21634 (|char#FromInt| 110)))) (
# _module.__default.protect |abc#0| (Lit_22656 (|Seq#Build| (|Seq#Build| (|Seq#Build| |Seq#Empty| ($Box_20912 (
# |char#FromInt| 97))) ($Box_20912 (|char#FromInt| 98))) ($Box_20912 (|char#FromInt| 99)))))


# pattern - ul $Unbox_? (_module.__default.protect T? reveal__module._default.protect ($Box_?

# pattern-ul $Unbox_? (_module.__default.protectToProve T? reveal__module._default.protectToProve ($Box_?

# ite (x % 2 == 0)
# assert x * (x + 1) == 2 * (x / 2 * (x + 1));
# assert x * (2 * (x / 2) + 2) == 2 * (x * (x / 2 + 1));
