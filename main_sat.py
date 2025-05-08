import time
import itertools
import csv
import os
from typing import List, Set, Dict
import random
from typing import List, Set

class SolverTimeout(Exception):
    pass

def generate_random_cnf(num_vars: int, num_clauses: int, inclusion_prob: float = 0.5) -> List[Set[int]]:
    cnf = []
    for _ in range(num_clauses):
        clause = set()
        for var in range(1, num_vars + 1):
            if random.random() < inclusion_prob:
                sign = random.choice([-1, 1])
                clause.add(sign * var)
        if not clause:
            # Avoid empty clauses by forcing at least one literal
            clause.add(random.choice([-1, 1]) * random.randint(1, num_vars))
        cnf.append(clause)
    return cnf


Literal = int
Clause = Set[Literal]
CNF = List[Clause]

def get_variables(cnf: CNF) -> Set[int]:
    return set(abs(lit) for clause in cnf for lit in clause)

#Brute Force Solver
def solve_brute_force(cnf: CNF, start_time = None, time_limit = 60) -> bool:
    if start_time is None:
        start_time = time.time()

    if time.time() - start_time > time_limit:
        raise SolverTimeout("DPLL solver timed out")
    variables = list(get_variables(cnf))
    for values in itertools.product([False, True], repeat=len(variables)):
        assignment = dict(zip(variables, values))
        if all(any((lit > 0 and assignment[abs(lit)]) or (lit < 0 and not assignment[abs(lit)]) for lit in clause) for clause in cnf):
            return True
    return False

#Davis–Putnam Solver (Resolution-based)
def resolve(c1: Clause, c2: Clause, var: int) -> Clause:
    return (c1 - {var}) | (c2 - {-var})

def resolve(ci: Set[int], cj: Set[int], literal: int) -> Set[int]:
    return (ci - {literal}) | (cj - {-literal})

#Resolution Solver
def solve_resolution(cnf: List[Set[int]], start_time=None, time_limit=60) -> bool:
    if start_time is None:
        start_time = time.time()

    if time.time() - start_time > time_limit:
        raise SolverTimeout("DPLL solver timed out")
    clauses = set(frozenset(c) for c in cnf)
    new = set()

    while True:
        pairs = list(itertools.combinations(clauses, 2))
        for (ci, cj) in pairs:
            ci_set, cj_set = set(ci), set(cj)
            for literal in ci_set:
                if -literal in cj_set:
                    resolvent = resolve(ci_set, cj_set, literal)
                    if not resolvent:
                        return False
                    new.add(frozenset(resolvent))
        if new.issubset(clauses):
            return True
        clauses |= new


def dp_solver(cnf: CNF, start_time=None, time_limit=60) -> bool:
    if start_time is None:
        start_time = time.time()

    if time.time() - start_time > time_limit:
        raise SolverTimeout("DPLL solver timed out")
    cnf = [set(clause) for clause in cnf]
    while True:
        vars_in_cnf = set(abs(lit) for clause in cnf for lit in clause)
        if not cnf:
            return True
        if any(len(clause) == 0 for clause in cnf):
            return False
        selected_var = next(iter(vars_in_cnf))
        new_clauses = []
        for c1 in cnf:
            if selected_var in c1:
                for c2 in cnf:
                    if -selected_var in c2:
                        resolvent = resolve(c1, c2, selected_var)
                        new_clauses.append(resolvent)
        cnf = [cl for cl in cnf if selected_var not in cl and -selected_var not in cl]
        cnf.extend(new_clauses)

#DPLL Solver
def dpll(cnf: CNF, assignment: Dict[int, bool] = {}, start_time = None, time_limit=60) -> bool:
    if start_time is None:
        start_time = time.time()

    if time.time() - start_time > time_limit:
        raise SolverTimeout("DPLL solver timed out")
    cnf = simplify(cnf, assignment)
    if any(len(clause) == 0 for clause in cnf):
        return False
    if not cnf:
        return True
    unit_literals = {next(iter(c)) for c in cnf if len(c) == 1}
    if unit_literals:
        new_assignment = assignment.copy()
        for lit in unit_literals:
            new_assignment[abs(lit)] = lit > 0
        return dpll(cnf, new_assignment)
    pure_literals = get_pure_literals(cnf)
    if pure_literals:
        new_assignment = assignment.copy()
        for lit in pure_literals:
            new_assignment[abs(lit)] = lit > 0
        return dpll(cnf, new_assignment)
    var = next(iter(get_variables(cnf)))
    for val in [True, False]:
        new_assignment = assignment.copy()
        new_assignment[var] = val
        if dpll(cnf, new_assignment):
            return True
    return False

def simplify(cnf: CNF, assignment: Dict[int, bool]) -> CNF:
    new_cnf = []
    for clause in cnf:
        new_clause = set()
        satisfied = False
        for lit in clause:
            var = abs(lit)
            val = assignment.get(var)
            if val is not None:
                if (lit > 0 and val) or (lit < 0 and not val):
                    satisfied = True
                    break
            else:
                new_clause.add(lit)
        if not satisfied:
            new_cnf.append(new_clause)
    return new_cnf

def get_pure_literals(cnf: CNF) -> Set[int]:
    lit_count = {}
    for clause in cnf:
        for lit in clause:
            lit_count[lit] = lit_count.get(lit, 0) + 1
    pure = set()
    for lit in lit_count:
        if -lit not in lit_count:
            pure.add(lit)
    return pure

#CSV Writing
def write_times_to_csv(filename: str, row: List):
    header_needed = not os.path.exists(filename)
    with open(filename, 'a', newline='') as csvfile:
        writer = csv.writer(csvfile)
        if header_needed:
            writer.writerow(["NumVars", "Status", "BruteForce", "DavisPutnam", "DPLL"])
        writer.writerow(row)

# --- Main Interface ---
def run_all_methods(cnf: CNF, output_file: str = "sat_times.csv"):
    times = []

    """start = time.time()
    print("starting brute force")
    sat_bf = solve_brute_force(cnf)
    times.append(time.time() - start)

    start = time.time()
    print("starting resolution")
    sat_res = solve_resolution(cnf)
    times.append(time.time() - start)

    start = time.time()
    print("starting dp")
    dp_solver(cnf)
    times.append(time.time() - start)"""

    # Brute Force
    try:
        print("starting brute force")
        start = time.time()
        sat_bf = solve_brute_force(cnf, start_time=start, time_limit=60)
        times.append(f"{time.time() - start:.6f}")
    except SolverTimeout:
        print("Brute force timed out!")
        times.append("TIMEOUT")
        sat_bf = None

    # Resolution
    try:
        print("starting resolution")
        start = time.time()
        sat_res = solve_resolution(cnf, start_time=start, time_limit=60)
        times.append(f"{time.time() - start:.6f}")
    except SolverTimeout:
        print("Resolution timed out!")
        times.append("TIMEOUT")
        sat_res = None

    # Davis–Putnam
    try:
        print("starting dp")
        start = time.time()
        dp_solver(cnf, start_time=start, time_limit=60)
        times.append(f"{time.time() - start:.6f}")
    except SolverTimeout:
        print("DP timed out!")
        times.append("TIMEOUT")

    try:
        start = time.time()
        result = dpll(cnf, start_time=start, time_limit=60)
        elapsed = time.time() - start
        times.append(f"{elapsed:.6f}")
    except SolverTimeout:
        print("DPLL timed out!")
        times.append("TIMEOUT")

    row = [len(get_variables(cnf)), "SAT" if result else "UNSAT"]
    write_times_to_csv(output_file, row + [f"{t:.6f}" if isinstance(t, float) else t for t in times])
    print(f"Done. CSV updated: {row + [f"{t:.6f}" if isinstance(t, float) else t for t in times]}")


# Example CNF: (x1 ∨ ¬x3) ∧ (¬x1 ∨ x2) ∧ (x3)
if __name__ == "__main__":
    import time

    while True:
        num_vars = 40
        num_clauses = 15
        inclusion_prob = 0.1 # tune this to taste

        cnf = generate_random_cnf(num_vars, num_clauses, inclusion_prob)

        print(f"\n🎲 Generated CNF with {num_vars} vars, {num_clauses} clauses")
        run_all_methods(cnf)
